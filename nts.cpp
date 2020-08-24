#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm-c/Core.h"
#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <utility>
#include <vector>
#include <vector>
#include <iostream>
#include "util.h"

// to compile:
// clang++ -O0 -c --debug -ggdb $(llvm-config --cxxflags) nts.cpp -o nts.o && clang++ nts.o -o nts $(llvm-config --ldflags --libs) -lpthread -ltinfo -Wall --debug -ggdb
/*... not this (goes to a.out, no debugging): // clang++ -O3 -c $(llvm-config --cxxflags) nts.cpp -o nts.o
// clang++ nts.o $(llvm-config --ldflags --libs) -lpthread -ltinfo
// in one line:
// clang++ -O3 -c $(llvm-config --cxxflags) nts.cpp -o nts.o && clang++ nts.o $(llvm-config --ldflags --libs) -lpthread -ltinfo...*/
// set environment variable: LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1

// to get llvm set up:
// https://clang.llvm.org/get_started.html # more up to date info
// https://llvm.org/docs/GettingStarted.html # tells about the -DLLVM_ENABLE_PROJECTS option
// note: The llvm library stuff accessible using c++ is called the "llvm c++ frontend".

// TODO list:
//  - make it so instead of codegen, fngen, typgen, we simply do a varinfogen, then typecheck tree structure, then perform final conversion to llvm IR (also macros fairly early on...)

//>-----------------------------------------------------------+
//>     Simple Error Handling                                 |
//>-----------------------------------------------------------+


void parse_error(const std::string msg, int lineno, FILE *f) {
  std::cout << "Parsing error on line " << lineno << ": " << msg << "\n";
  fclose(f);
  exit(0);
}



//>-----------------------------------------------------------+
//>     Lexer                                                 |
//>-----------------------------------------------------------+

enum Token {
  tok_eof  = -1, // end of file
  tok_opar = -2, // (
  tok_cpar = -3, // )
  tok_obrk = -4, // [
  tok_cbrk = -5, // ]
  tok_quot = -6, // '
  tok_iden = -7, // identifier
  tok_int  = -8, // integer
  // TODO: chr, float, complex
};

enum LexerState {
  ls_start    = 0,
  ls_ident    = 1,
  ls_numeral  = 2,
  ls_minus    = 3,
  ls_err      = 4,
};

static std::string iden_str;  // filled in if tok_iden
static int int_val;           // filled in if tok_int
static int line_no = 1;       // current line number in parsing

bool isalnumsym(char c) {
  if (isalpha(c) || isdigit(c) || c == '+' || c == '-' || c == '_' ||
          c == '*' || c == '/' || c == '&' || c == '|' || c == '@' ||
          c == '?' || c == '=' || c == '<' || c == '>' || c == '!')
    return true;
  else
    return false;
}

static int gettok(FILE *f) {
  char c = fgetc(f);
  // ignore whitespace and comments
  while (isspace(c) || c == '#') {
    if (c == '\n') line_no++; // '\n' counts as whitespace, so we can keep track of line numbers here
    if (c == '#') {
      do c = fgetc(f); while (c != EOF && c != '\n' && c != '\r' && c != 0);
    } else {
      c = fgetc(f);
    }
  }
  // check for end of string / file
  if (c == 0 || c == EOF) return tok_eof;
  // delimiters
  if (c == '(')  { return tok_opar; }
  if (c == ')')  { return tok_cpar; }
  if (c == '[')  { return tok_obrk; }
  if (c == ']')  { return tok_cbrk; }
  if (c == '\'') { return tok_quot; }
  // indentifier or numeber
  if (isalnumsym(c)) {
    std::string acc_str;
    int state = ls_start;
    do {
      switch (state) {
        case ls_start:
          if (c == '-')
            state = ls_minus;
          else if (isdigit(c))
            state = ls_numeral;
          else
            state = ls_ident;
          break;
        case ls_minus:
          if (isdigit(c))
            state = ls_numeral;
          else
            state = ls_ident;
          break;
      }
      acc_str.push_back(c);
      c = fgetc(f);
    } while (isalnumsym(c));
    ungetc(c, f); // put back the final character c not a part of the identifier/number
    switch (state) {
      case ls_minus:
      case ls_ident:
        iden_str = acc_str;
        return tok_iden;
      case ls_numeral:
        int_val = strtol(acc_str.c_str(), NULL, 0);
        if (errno != 0) parse_error("invalid number literal", line_no, f);
        return tok_int;
    }
  }
  parse_error("invalid character", line_no, f);
  return 0;
}


//>-----------------------------------------------------------+
//>     Type System                                           |
//>-----------------------------------------------------------+


enum TypCons { // ways to construct a typ
  tc_fail     = 0, // denotes an invalid typ, we choose integer rep of 0 so it is the default
  tc_void     = 1, // void typ
  tc_typ      = 2, // the typ of any other typ
  tc_bit      = 3, // 1 bit (boolean)
  tc_int      = 4, // 64 bit integer
  tc_fn       = 8,  // function
  tc_tup      = 9,  // tuple
  tc_tens     = 10, // tensor
};

typedef struct Typ {
  TypCons tc;
  std::vector<struct Typ> t1;
  std::vector<struct Typ> t2;
  std::vector<int> szs;
} Typ;

Typ typ_from_tc(TypCons tc) {
  Typ ans{};
  ans.tc = tc;
  return ans;
}

typedef struct VarInfo {
  Typ typ;              // The typ of this var
  llvm::Value *val;     // The value of this var, if it is a value
  llvm::Function *fun;  // The value of this var, if it is a function
  Typ typval;           // The value of this var, if it is a typ
  llvm::Value *loc;     // The location of this var, if applicable (if val is NULL, we load from this location)
  std::vector<llvm::Value *> dimvals; // the values of the unknown indices of the var, if it is a tensor
} VarInfo;

VarInfo var_info_from_value(llvm::Value *val, Typ typ) { 
  VarInfo ans = {};
  ans.typ = typ;
  ans.val = val;
  return ans;
}
VarInfo var_info_from_function(llvm::Function *fun, Typ typ) { 
  VarInfo ans = {};
  ans.typ = typ;
  ans.fun  = fun;
  return ans;
}
VarInfo var_info_from_typ(Typ typval) {
  VarInfo ans = {};
  ans.typ = typ_from_tc(tc_typ);
  ans.typval = typval;
  return ans;
}
VarInfo var_info_fail() {
  VarInfo ans = {};
  ans.typ = typ_from_tc(tc_fail);
  return ans;
}
VarInfo var_info_void() {
  VarInfo ans = {};
  ans.typ = typ_from_tc(tc_void);
  return ans;
}

llvm::Function *vi_get_fn(VarInfo vi) {
  switch (vi.typ.tc) {
    case tc_fn:
      return vi.fun;
    default:
      return NULL;
  }
}

Typ vi_get_typ(VarInfo vi) {
  switch (vi.typ.tc) {
    case tc_typ:
      return vi.typval;
    default:
      return typ_from_tc(tc_fail);
  }
}



//>-----------------------------------------------------------+
//>     AST Classes                                           |
//>-----------------------------------------------------------+

class ExprCall; // predeclaration

class Expr {
public:
  int kind = 0;
  int line = 0;
  bool quoted = false;
  Expr(int kind, int line) : kind(kind), line(line) {}
  virtual ~Expr() {}
  virtual void show() {}
  virtual ExprCall *make_iter(std::vector<ExprCall *> &curr_stack) { return NULL; } // throw error
  virtual int *get_int() { return NULL; }
  virtual std::string *get_iden() { return NULL; }
  virtual std::vector<Expr *> *get_elems() { return NULL; }
  virtual VarInfo codegen() = 0;
  virtual void fail(std::string msg) {
    std::cout << "Error in expression on line " << line << ": " << msg << "\n";
    exit(0);
  }
};

class ExprInt : public Expr {
public:
  int val;
  ExprInt(int val, int line) : val(val), Expr(1, line) {}
  void show() {std::cout << " " << val << " ";}
  int *get_int() { return &val; }
  virtual VarInfo codegen();
};

class ExprIden : public Expr {
public:
  std::string name;
  ExprIden(const std::string &name, int line) : name(name), Expr(2, line) {}
  void show() {
    if (quoted)
      std::cout << " '" << name << " ";
    else
      std::cout << " " << name << " ";
  }
  std::string *get_iden() { return &name; }
  virtual VarInfo codegen();
};

class ExprCall : public Expr {
public:
  std::vector<Expr*> elems;
  ExprCall(int line) : Expr(3, line) {}
  void show() {
    if (quoted)
      std::cout << " '( ";
    else
      std::cout << " ( ";
    for (Expr *expr : elems) expr->show();
    std::cout << " )";
  }
  ExprCall *make_iter(std::vector<ExprCall*> &curr_stack) {
    ExprCall *ans = new ExprCall(line);
    ans->elems.push_back(new ExprIden("tfor", line)); // "tfor" means tensor for loop expression
    ExprCall *itervars = new ExprCall(line);
    curr_stack.push_back(itervars);
    ans->elems.push_back(itervars);
    ans->elems.push_back(this);
    return ans;
  }
  std::vector<Expr *> *get_elems() { return &elems; }
  virtual VarInfo codegen();
};



//>-----------------------------------------------------------+
//>     Parser                                                |
//>-----------------------------------------------------------+

enum Delim {
  dl_file = 0,
  dl_paren = 1,
  dl_brkt = 2,
  dl_quot = 3,
};

ExprCall *parse(FILE *f) {
  int tok = 0;
  // program is the thing we write to:
  ExprCall *program = new ExprCall(0);
  program->elems.push_back(new ExprIden("{main_program_code}", 0)); // curly braces so that user cannot call this fn
  // make stacks to keep track of program structure:
  std::vector<Delim> delim_stack; delim_stack.push_back(dl_file);
  std::vector<ExprCall*> curr_stack; curr_stack.push_back(program);
  // keep track of quoting
  bool quoting = false;
  // parse:
  while (tok != tok_eof) {
    tok = gettok(f);
    ExprCall *tmp_expr;
    switch (tok) {
      case tok_opar:
        tmp_expr = new ExprCall(line_no);
        curr_stack.back()->elems.push_back(tmp_expr);
        curr_stack.push_back(tmp_expr);
        delim_stack.push_back(dl_paren);
        break;
      case tok_cpar:
        if (delim_stack.back() != dl_paren)
          parse_error("did not expect to see ')' here", line_no, f);
        curr_stack.pop_back();
        delim_stack.pop_back();
        break;
      case tok_obrk:
        tmp_expr = curr_stack.back()->elems.back()->make_iter(curr_stack);
        if (tmp_expr == NULL)
          parse_error("did not expect to see '[' here, square brackets should appear after an s-expression", line_no, f);
        curr_stack[curr_stack.size() - 2]->elems.pop_back();
        curr_stack[curr_stack.size() - 2]->elems.push_back(tmp_expr);
        delim_stack.push_back(dl_brkt);
        break;
      case tok_cbrk:
        if (delim_stack.back() != dl_brkt)
          parse_error("did not expect to see ']' here", line_no, f);
        curr_stack.pop_back();
        delim_stack.pop_back();
        break;
      case tok_iden:
        curr_stack.back()->elems.push_back(new ExprIden(iden_str, line_no));
        break;
      case tok_int:
        curr_stack.back()->elems.push_back(new ExprInt(int_val, line_no));
        break;
      case tok_quot:
        delim_stack.push_back(dl_quot);
        break;
    }
    if (delim_stack.back() == dl_quot) {
      if (quoting) {
        curr_stack.back()->elems.back()->quoted = true;
        quoting = false;
        delim_stack.pop_back();
      } else {
        quoting = true; // only start quoting once we have moved past the ' symbol itself
      }
    }
  }
  return program;
}


//>-----------------------------------------------------------+
//>     Code Generation                                       |
//>-----------------------------------------------------------+

static llvm::LLVMContext TheContext;
static llvm::IRBuilder<> Builder(TheContext);
static llvm::Module TheModule("my_module", TheContext);
static stackmap<std::string, VarInfo> GlobalValues(NULL);
static stackmap<std::string, VarInfo> *NamedValues = &GlobalValues;


// useful function for generating int constants:
llvm::Value *iconst(int val) {
  return llvm::ConstantInt::get(TheContext, llvm::APInt(64, val, true));
}
// useful function for generating bit constants:
llvm::Value *bconst(int val) {
  return llvm::ConstantInt::get(TheContext, llvm::APInt(1, val, true));
}


llvm::Type *typ_conv(Typ t) {
  // convert Typs to llvm types
  switch (t.tc) {
    case tc_void: // void typ
      return llvm::Type::getVoidTy(TheContext);
    case tc_int: // integer typ
      return llvm::Type::getInt64Ty(TheContext);
    case tc_tup: { // tuple (i.e. struct) typ
      std::vector<llvm::Type *> elem_ltypes = std::vector<llvm::Type *>();
      for (Typ subtyp : t.t1) {
        elem_ltypes.push_back(typ_conv(subtyp));
      }
      return llvm::StructType::create(elem_ltypes);
    }
    case tc_tens: {
      int totsz = 1;
      for (int dimsz : t.szs) {
        totsz *= dimsz;
        if (dimsz == -1) // dynamic dimension
          return llvm::ArrayType::get(typ_conv(t.t1[0]), 0); // TODO: should actually pass dynamic sizes along with array as a struct
      }
      return llvm::ArrayType::get(typ_conv(t.t1[0]), totsz);
    }
    default:
      return NULL; // TODO: should probably fail here...
  }
  // TODO: arrays, function types, etc
}

bool is_subtyp(Typ t1, Typ t2) {
  // determine if t1 can be considered a subtyp of t2
  switch (t2.tc) {
    case tc_void:
      return (t1.tc == tc_void);
    case tc_int:
      return (t1.tc == tc_int);
    case tc_tup: {
      if (t1.tc != tc_tup) return false;
      int size = t2.t1.size();
      if (t1.t1.size() != size) return false;
      for (int i = 0; i < size; i++) {
        if (!is_subtyp(t1.t1[i], t2.t1[i])) return false;
      }
      return true;
    }
    case tc_tens: {
      if (t1.tc != tc_tens) return false;
      if (!is_subtyp(t1.t1[0], t2.t1[0])) return false;
      int dims = t2.szs.size();
      for (int i = 0; i < dims; i++) {
        if (t1.szs[i] != t2.szs[i]) {
          if (t2.szs[i] != -1) return false;
        } // -1 means arbitrary size, so we can accept any specific size
      }
      return true;
    }
    default:
      return false;
  }
}


VarInfo alloc_typ(VarInfo vi_typ) {
  // allocate space for a varible with typ (and any auxilliary info) given by typ
  VarInfo ans = {};
  switch (vi_typ.typval.tc) {
    case tc_tens: {
      int prod_sz = 1;
      for (int dimsz : vi_typ.typval.szs) { // static dim sizes
        if (dimsz >= 0) prod_sz *= dimsz;
      }
      llvm::Value *finalsz = iconst(prod_sz);
      for (llvm::Value *dimsz2 : vi_typ.dimvals) { // dynamic dim sizes
        finalsz = Builder.CreateMul(finalsz, dimsz2, "computeszmultmp");
      }
      llvm::Value *allocinst = Builder.CreateAlloca(typ_conv(vi_typ.typval.t1[0]), 0, finalsz, "alloctens");
      ans.typ = vi_typ.typval;
      ans.val = allocinst;
      ans.dimvals = vi_typ.dimvals; // TODO: this is very inelegant, should assign struct fields for this or something
      return ans;
    }
    default: {
      llvm::Value *allocinst = Builder.CreateAlloca(typ_conv(vi_typ.typval), 0, iconst(1));
      ans.typ = vi_typ.typval;
      ans.val = allocinst;
      return ans;
    }
  }
}


llvm::Value *vi_get_val(VarInfo vi) { //TODO TODO TODO TODO: replace currently existing uses of ".val" with this
  switch (vi.typ.tc) {
    case tc_tens: // TODO: add more here as time goes on...
    case tc_int:
    case tc_bit:
      if (vi.val != NULL) { // either return the explicit value...
        return vi.val;
      } else { // or dereference the pointer to the location where the value is held
        return Builder.CreateLoad(vi.loc);
      }
    default:
      return NULL;
  }
}


// prefill some named values:
void prefill_builtins() {
  // basic type definitions:
  NamedValues->set("bit", var_info_from_typ(typ_from_tc(tc_bit)));
  NamedValues->set("int", var_info_from_typ(typ_from_tc(tc_int)));
  NamedValues->set("void", var_info_from_typ(typ_from_tc(tc_void)));
  
  // define true / false
  NamedValues->set("false", var_info_from_value(bconst(0), typ_from_tc(tc_bit)));
  NamedValues->set("true",  var_info_from_value(bconst(1), typ_from_tc(tc_bit)));
  
  // steal the putchar function from C
  std::vector<llvm::Type *> args(1, llvm::Type::getInt64Ty(TheContext));
  Typ fntyp = typ_from_tc(tc_fn); // create a new empty function type
  fntyp.t1.push_back(typ_from_tc(tc_int)); // add argument typs
  fntyp.t2.push_back(typ_from_tc(tc_int)); // add return typ
  llvm::FunctionType *FT = llvm::FunctionType::get(
    llvm::Type::getInt64Ty(TheContext), args, false);
  llvm::Function *F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, "putchar", TheModule);
  NamedValues->set("putchar", var_info_from_function(F, fntyp));
  // TODO: steal malloc, free from C
}



// codegen for the various expression types:


VarInfo ExprInt::codegen() {
  llvm::Value *lval = iconst(val);
  return var_info_from_value(lval, typ_from_tc(tc_int));
}


VarInfo ExprIden::codegen() {
  if (NamedValues->has(name)) {
    return NamedValues->at(name);
  }
  fail("variable " + name + " is not defined here");
  return var_info_fail();
}


VarInfo ExprCall::codegen() {
  // TODO: special handling for for loops, def, <-, lambda, tensors, +, -, *, /, etc.
  int size = elems.size();
  if (size == 0) return var_info_fail(); // illegal
  std::string *iden = elems[0]->get_iden();
  if (iden != NULL) { // check for and handle builtins...
    // TODO: assertions for argument number and structure for builtins
    // TODO: clear out the repetition...
    // TODO: add floats, handle overloading (of bits, ints, eventually floats)
    if (iden->compare("+") == 0) { // handle addition
      llvm::Value *argl = vi_get_val(elems[1]->codegen());
      if (argl == NULL) fail("could not determine value of left argument");
      llvm::Value *argr = vi_get_val(elems[2]->codegen());
      if (argr == NULL) fail("could not determine value of right argument");
      llvm::Value *lval = Builder.CreateAdd(argl, argr, "addtmp");
      return var_info_from_value(lval, typ_from_tc(tc_int));
    }
    if (iden->compare("-") == 0) { // handle negation, subtraction
      if (elems.size() == 2) { // negation
        llvm::Value *arg = vi_get_val(elems[1]->codegen());
        if (arg == NULL) fail("could not determine value of argument");
        llvm::Value *lval = Builder.CreateNeg(arg, "negtmp");
        return var_info_from_value(lval, typ_from_tc(tc_int));
      } else {
        llvm::Value *argl = vi_get_val(elems[1]->codegen());
        if (argl == NULL) fail("could not determine value of left argument");
        llvm::Value *argr = vi_get_val(elems[2]->codegen());
        if (argr == NULL) fail("could not determine value of right argument");
        llvm::Value *lval = Builder.CreateSub(argl, argr, "subtmp");
        return var_info_from_value(lval, typ_from_tc(tc_int));
      }
    }
    if (iden->compare("*") == 0) { // handle multiplication
      llvm::Value *argl = vi_get_val(elems[1]->codegen());
      if (argl == NULL) fail("could not determine value of left argument");
      llvm::Value *argr = vi_get_val(elems[2]->codegen());
      if (argr == NULL) fail("could not determine value of right argument");
      llvm::Value *lval = Builder.CreateMul(argl, argr, "multmp");
      return var_info_from_value(lval, typ_from_tc(tc_int));
    }
    if (iden->compare("/") == 0) { // handle division
      llvm::Value *argl = vi_get_val(elems[1]->codegen());
      if (argl == NULL) fail("could not determine value of left argument");
      llvm::Value *argr = vi_get_val(elems[2]->codegen());
      if (argr == NULL) fail("could not determine value of right argument");
      llvm::Value *lval = Builder.CreateSDiv(argl, argr, "divtmp"); // non-exact signed division
      return var_info_from_value(lval, typ_from_tc(tc_int));
    }
    if (iden->compare("/r") == 0) { // remainder after division
      llvm::Value *argl = vi_get_val(elems[1]->codegen());
      if (argl == NULL) fail("could not determine value of left argument");
      llvm::Value *argr = vi_get_val(elems[2]->codegen());
      if (argr == NULL) fail("could not determine value of right argument");
      llvm::Value *lval = Builder.CreateSRem(argl, argr, "remtmp");
      return var_info_from_value(lval, typ_from_tc(tc_int));
    }
    if (iden->compare("mod") == 0) { // handle modulus function (mod 3 x) gives y in {0,1,2} st y = x (mod 3)
      llvm::Value *argl = vi_get_val(elems[1]->codegen());
      if (argl == NULL) fail("could not determine value of left argument"); // modulus
      llvm::Value *argr = vi_get_val(elems[2]->codegen());
      if (argr == NULL) fail("could not determine value of right argument"); // x
      llvm::Value *lval = Builder.CreateSRem(argr, argl, "modtmpsgn"); // possibly negative remainder
      lval = Builder.CreateAdd(lval, argl, "modtmpadd");
      lval = Builder.CreateSRem(lval, argl, "modtmp"); // positive remainder
      return var_info_from_value(lval, typ_from_tc(tc_int));
    }
    if (iden->compare("=") == 0) { // compare for equality
      llvm::Value *argl = vi_get_val(elems[1]->codegen());
      if (argl == NULL) fail("could not determine value of left argument");
      llvm::Value *argr = vi_get_val(elems[2]->codegen());
      if (argr == NULL) fail("could not determine value of right argument");
      llvm::Value *lval = Builder.CreateICmpEQ(argl, argr, "compeqtmp");
      return var_info_from_value(lval, typ_from_tc(tc_bit));
    }
    if (iden->compare("!=") == 0) { // compare for non-equality
      llvm::Value *argl = vi_get_val(elems[1]->codegen());
      if (argl == NULL) fail("could not determine value of left argument");
      llvm::Value *argr = vi_get_val(elems[2]->codegen());
      if (argr == NULL) fail("could not determine value of right argument");
      llvm::Value *lval = Builder.CreateICmpEQ(argl, argr, "compnetmp");
      return var_info_from_value(lval, typ_from_tc(tc_bit));
    }
    if (iden->compare(">") == 0) { // compare greater than
      llvm::Value *argl = vi_get_val(elems[1]->codegen());
      if (argl == NULL) fail("could not determine value of left argument");
      llvm::Value *argr = vi_get_val(elems[2]->codegen());
      if (argr == NULL) fail("could not determine value of right argument");
      llvm::Value *lval = Builder.CreateICmpSGT(argl, argr, "compgttmp");
      return var_info_from_value(lval, typ_from_tc(tc_bit));
    }
    if (iden->compare(">=") == 0) { // compare greater than or equal
      llvm::Value *argl = vi_get_val(elems[1]->codegen());
      if (argl == NULL) fail("could not determine value of left argument");
      llvm::Value *argr = vi_get_val(elems[2]->codegen());
      if (argr == NULL) fail("could not determine value of right argument");
      llvm::Value *lval = Builder.CreateICmpSGE(argl, argr, "compgetmp");
      return var_info_from_value(lval, typ_from_tc(tc_bit));
    }
    if (iden->compare("<") == 0) { // compare less than
      llvm::Value *argl = vi_get_val(elems[1]->codegen());
      if (argl == NULL) fail("could not determine value of left argument");
      llvm::Value *argr = vi_get_val(elems[2]->codegen());
      if (argr == NULL) fail("could not determine value of right argument");
      llvm::Value *lval = Builder.CreateICmpSLT(argl, argr, "complttmp");
      return var_info_from_value(lval, typ_from_tc(tc_bit));
    }
    if (iden->compare("=<") == 0) { // compare less than or equal
      llvm::Value *argl = vi_get_val(elems[1]->codegen());
      if (argl == NULL) fail("could not determine value of left argument");
      llvm::Value *argr = vi_get_val(elems[2]->codegen());
      if (argr == NULL) fail("could not determine value of right argument");
      llvm::Value *lval = Builder.CreateICmpSLE(argl, argr, "completmp");
      return var_info_from_value(lval, typ_from_tc(tc_bit));
    }
    // TODO: bitwise &, |, ^, !. (for both bit, int typs)
    if (iden->compare("predef") == 0) { // allow for predefining of functions (for externs, recursion, mutual recursion, etc.)
      Typ fntyp = typ_from_tc(tc_fn);
      Typ rettyp = vi_get_typ(elems[1]->codegen());
      if (rettyp.tc == tc_fail) fail("could not figure out return type");
      fntyp.t2.push_back(rettyp); // set return typ
      std::string *fnname = elems[2]->get_iden(); // get the name of the function
      if (fnname == NULL) fail("function name must be a symbol, not numbers or calls");
      std::vector<Expr *> *arglist = elems[3]->get_elems();
      int arg_num = arglist->size();
      std::vector<llvm::Type *> arg_ltypes;
      for (int i = 0; i < arg_num; i++) {
        Typ argtyp = vi_get_typ(arglist->at(i)->codegen());
        fntyp.t1.push_back(argtyp);  // set argument typs
        arg_ltypes.push_back(typ_conv(argtyp));
      }
      llvm::FunctionType *FT = llvm::FunctionType::get(
        typ_conv(rettyp), arg_ltypes, false);
      llvm::Function *F = TheModule.getFunction(*fnname);
      if (!F) { // if F does not already exist, we create it
        F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, *fnname, TheModule);
      } else {
        // TODO: check that signatures match
      }
      NamedValues->set(*fnname, var_info_from_function(F, fntyp));
      return var_info_void();
    }
    if (iden->compare("def") == 0) {
      int i;
      // prepare signature
      Typ fntyp = typ_from_tc(tc_fn);
      Typ rettyp = vi_get_typ(elems[1]->codegen());
      if (rettyp.tc == tc_fail) fail("could not figure out return type");
      fntyp.t2.push_back(rettyp); // set return typ
      std::string *fnname = elems[2]->get_iden(); // get the name of the function
      if (fnname == NULL) fail("function name must be a symbol, not numbers or calls");
      std::vector<Expr *> *arglist = elems[3]->get_elems();
      int arg_num = arglist->size() / 2;
      std::vector<llvm::Type *> arg_ltypes;
      std::vector<std::string> argnames;
      for (i = 0; i < arg_num; i++) {
        Typ argtyp = vi_get_typ(arglist->at(2*i)->codegen());
        fntyp.t1.push_back(argtyp);  // set argument typs TODO: handle case with fail typ
        arg_ltypes.push_back(typ_conv(argtyp)); // set llvm types for arguments
        std::string *argnm = arglist->at(2*i + 1)->get_iden(); // get argument names
        if (argnm == NULL) fail("parameter names must be identifiers, not numbers or calls");
        argnames.push_back(argnm->substr());
      }
      llvm::FunctionType *FT = llvm::FunctionType::get(
        typ_conv(rettyp), arg_ltypes, false);
      
      llvm::Function *F = TheModule.getFunction(*fnname);
      if (!F) { // if F does not already exist, we create it
        F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, *fnname, TheModule);
      } else {
        // TODO: check that signatures match
      }
      // TODO: above code is redundant with predef, and should be pulled out info function or something...
      i = 0; for (auto &Arg : F->args())
        Arg.setName(argnames[i++]);
      // set up fn args and body
      llvm::BasicBlock *BB = llvm::BasicBlock::Create(TheContext, "entry", F);
      Builder.SetInsertPoint(BB);
      stackmap<std::string, VarInfo> nv(NamedValues); // new stackmap for arguments and local variables of this fn...
      NamedValues = &nv;
      i = 0; for (auto &Arg : F->args())
        NamedValues->set(std::string(Arg.getName()), var_info_from_value(&Arg, fntyp.t1[i++]));
      // define body
      VarInfo vi_ret = elems[4]->codegen();
      llvm::Value *retval = vi_get_val(vi_ret);
      if (fntyp.t2[0].tc == tc_void) retval = NULL; // handle return from void function (can ignore type of body function)
      // TODO: check that the typs match up
      // cleanup
      Builder.CreateRet(retval);
      llvm::verifyFunction(*F);
      NamedValues = nv.pop(); // go back to normal
      // add function to list of defined values
      NamedValues->set(*fnname, var_info_from_function(F, fntyp));
      return var_info_void(); // definition expressions yield void
    }
    if (iden->compare("if") == 0) {
      if (size != 4) fail("if expression takes format of (if (condition) (then) (else))");
      // condition
      VarInfo vi_cond = elems[1]->codegen();
      llvm::Value *bool_cond = vi_get_val(vi_cond);
      // figure out where we are
      llvm::Function *TheFunction = Builder.GetInsertBlock()->getParent();
      // setup blocks
      llvm::BasicBlock *ThenBB  = llvm::BasicBlock::Create(TheContext, "then", TheFunction); // insert then block into current function
      llvm::BasicBlock *ElseBB  = llvm::BasicBlock::Create(TheContext, "else");
      llvm::BasicBlock *MergeBB = llvm::BasicBlock::Create(TheContext, "ifcont");
      Builder.CreateCondBr(bool_cond, ThenBB, ElseBB);
      // then
      Builder.SetInsertPoint(ThenBB);
      VarInfo vi_then = elems[2]->codegen(); // may change current block
      Builder.CreateBr(MergeBB);
      ThenBB = Builder.GetInsertBlock();     // get new value of current block (if changed)
      // else
      TheFunction->getBasicBlockList().push_back(ElseBB);
      Builder.SetInsertPoint(ElseBB);
      VarInfo vi_else = elems[3]->codegen(); // may change current block
      Builder.CreateBr(MergeBB);
      ElseBB = Builder.GetInsertBlock();     // get new value of current block (if changed)
      // compute return typ (assuming typ of else is same)  TODO: return sum type when types of then/else expressions are unequal
      Typ anstyp = vi_then.typ;
      //merge
      TheFunction->getBasicBlockList().push_back(MergeBB);
      Builder.SetInsertPoint(MergeBB);
      llvm::PHINode *ans = Builder.CreatePHI(typ_conv(anstyp), 2, "iftmp");
      ans->addIncoming(vi_get_val(vi_then), ThenBB);
      ans->addIncoming(vi_get_val(vi_else), ElseBB);
      return var_info_from_value(ans, anstyp);
    }
    if (iden->compare("for") == 0) { // simple for loop expression
      // simple for loop: (for i (max) (expr)) ==> vector of length max
      std::string *loopvar_iden = elems[1]->get_iden(); // name of loop variable...
      if (loopvar_iden == NULL) fail("expected a symbol for the iteration variable name");
      // compute max number of iterations
      VarInfo maxiter = elems[2]->codegen();
      if (!is_subtyp(maxiter.typ, typ_from_tc(tc_int))) fail("number of iterations must be an integer");
      // loop starts from 0...
      llvm::Value *startval = iconst(0);
      llvm::Function *TheFunction = Builder.GetInsertBlock()->getParent();
      llvm::BasicBlock *PreheaderBB = Builder.GetInsertBlock();
      llvm::BasicBlock *LoopBB  = llvm::BasicBlock::Create(TheContext, "loop", TheFunction);
      llvm::BasicBlock *AfterBB = llvm::BasicBlock::Create(TheContext, "afterloop");
      // Insert an explicit fall through from the current block to the LoopBB (if maxiter <= 0, we go straight to the end).
      llvm::Value *skiploop = Builder.CreateICmpSLE(vi_get_val(maxiter), iconst(0), "loopcond");
      Builder.CreateCondBr(skiploop, AfterBB, LoopBB);
      // Start insertion in LoopBB.
      Builder.SetInsertPoint(LoopBB);
      // Start the PHI node with an entry for Start.
      llvm::PHINode *loopvar = Builder.CreatePHI(llvm::Type::getInt64Ty(TheContext),
                                      2, *loopvar_iden);
      loopvar->addIncoming(startval, PreheaderBB);
      stackmap<std::string, VarInfo> nv(NamedValues); // new stackmap for arguments and local variables of this fn...
      NamedValues = &nv;
      NamedValues->set(*loopvar_iden, var_info_from_value(loopvar, typ_from_tc(tc_int)));
      // loop body
      VarInfo body = elems[3]->codegen();
      llvm::Value *loopvar_next = Builder.CreateAdd(loopvar, // increment loopvar
          iconst(1), "nextvar");
      llvm::Value *endcond = Builder.CreateICmpSLT(loopvar_next, vi_get_val(maxiter), "loopcond");
      llvm::BasicBlock *LoopEndBB = Builder.GetInsertBlock();
      // Insert the conditional branch into the end of LoopEndBB.
      Builder.CreateCondBr(endcond, LoopBB, AfterBB);
      // Any new code will be inserted in AfterBB.
      TheFunction->getBasicBlockList().push_back(AfterBB);
      Builder.SetInsertPoint(AfterBB);
      // add other incoming path to loopvar phi node
      loopvar->addIncoming(loopvar_next, LoopEndBB);
      // clean up NamedValues
      NamedValues = nv.pop();
      return var_info_void(); // TODO: make for loops return vectors, not void
    }
    if (iden->compare("do") == 0) { // do all the things in a block, return the last one
      llvm::Function *TheFunction = Builder.GetInsertBlock()->getParent();
      VarInfo ans = {};
      stackmap<std::string, VarInfo> nv(NamedValues); // new stackmap for variables local to this do block
      NamedValues = &nv;
      for (int i = 1; i < size; i++) {
        ans = elems[i]->codegen();
        Builder.SetInsertPoint(&(TheFunction->getBasicBlockList().back()));
      }
      // clean up NamedValues
      NamedValues = nv.pop();
      return ans;
    }
    if (iden->compare("make") == 0) { // allocate a new variable...
      std::string *iden = elems[2]->get_iden();
      if (iden == NULL) fail("should provide symbol to identify variable");
      VarInfo vartyp = elems[1]->codegen();
      if (vartyp.typ.tc != tc_typ) fail("should provide typ of variable to make");
      NamedValues->set(*iden, alloc_typ(vartyp));
      return var_info_void();
    }
    if (iden->compare("<-") == 0) { // assign to a variable...
      fail("'<-' not implemented");
      return var_info_fail();
    }
    if (iden->compare("{main_program_code}") == 0) {
      llvm::Type *rettyp = llvm::Type::getInt64Ty(TheContext);
      std::vector<llvm::Type *> argtyps; // this will stay empty
      llvm::FunctionType *FT = llvm::FunctionType::get(
        rettyp, argtyps, false);
      llvm::Function *F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, "main", TheModule);
      llvm::BasicBlock *BB = llvm::BasicBlock::Create(TheContext, "main_program_code", F);
      Builder.SetInsertPoint(BB);
      llvm::Value *retval;
      for (int i = 1; i < size; i++) {
        retval = vi_get_val(elems[i]->codegen());
        Builder.SetInsertPoint(&(F->getBasicBlockList().back()));
      }
      retval = iconst(0);
      Builder.CreateRet(retval);
      llvm::verifyFunction(*F);
      Typ fntyp = typ_from_tc(tc_fn);
      fntyp.t2.push_back(typ_from_tc(tc_int));
      return var_info_from_function(F, fntyp);
    }
  }
  // Case: calling an already defined function / accessing an element of a tensor (TODO) / constructing a tensor typ
  VarInfo callee = elems[0]->codegen();
  switch (callee.typ.tc) {
    case tc_fn: { // call a function
      llvm::Function *func = vi_get_fn(callee);
      if (func == NULL) fail("could not call first element of expression as a function");
      // TODO: check argument typs and counts
      std::vector<llvm::Value *> args_llvm;
      args_llvm.reserve(size);
      for (int i = 1; i < size; i++) {
        llvm::Value *val = vi_get_val(elems[i]->codegen());
        if (val == NULL) fail("function was passed a non-value");
        args_llvm.push_back(val);
      }
      llvm::Value *lval = Builder.CreateCall(func, args_llvm);
      return var_info_from_value(lval, callee.typ.t2[0]);
    }
    case tc_typ: { // get a tensor typ (supplemented with values for variable size dims)
      Typ anstyp = typ_from_tc(tc_tens);
      VarInfo ans = {};
      anstyp.t1.push_back(callee.typval); // set element typ
      int size = elems.size();
      for (int i = 1; i < size; i++) {
        int *dimsz = elems[i]->get_int();
        if (dimsz == NULL) {
          anstyp.szs.push_back(-1);
          VarInfo vi_dimsz = elems[i]->codegen();
          if (vi_dimsz.typ.tc != tc_int) fail("expected dimension size to be an integer");
          ans.dimvals.push_back(vi_get_val(vi_dimsz));
        } else {
          anstyp.szs.push_back(*dimsz);
        }
      }
      ans.typ = typ_from_tc(tc_typ);
      ans.typval = anstyp;
      return ans;
    }
    case tc_tens: { // index into a tensor
      VarInfo ans = {};
      std::vector<VarInfo> indices;
      int size = elems.size();
      for (int i = 1; i < size; i++) { // compute varinfo for each index
        indices.push_back(elems[i]->codegen());
      }
      llvm::Value *index = iconst(0);
      int dimval_count = 0;
      for (int i = 0; i < size - 1; i++) { // compute overall index
        if (i > 0) { // don't need to worry about first dimension size... (until inbounds modding implemented)
          if (callee.typ.szs[i] >= 0) {
            index = Builder.CreateMul(index, iconst(callee.typ.szs[i]), "dimmultmp");
          } else {
            index = Builder.CreateMul(index, callee.dimvals[dimval_count], "dimmultmp");
            dimval_count++;
          }
        }
        index = Builder.CreateAdd(index, vi_get_val(indices[i]), "idxaddtmp");
      }
      llvm::Value *ptr = Builder.CreateGEP(vi_get_val(callee), index, "GEPtmp");
      // construct the result
      ans.typ = callee.typ.t1[0]; // get typ of tensor elements
      ans.loc = ptr; // pass by location, not value
      return ans;
      // TODO: note that we can't handle tensors of tensors like this: should pass dynamic dimsizes with tensors as struct
      // TODO: implement atuomatic tensor size inference here
      // TODO: partial indexing
      // TODO: force inbounds access with modular arithmetic
    }
    default:
      fail("first element of s expr can't be called or accessed, and is not a typ");
      return var_info_fail();
  }
}



// TODO: type checking...


//>-----------------------------------------------------------+
//>     Compilation Function                                  |
//>-----------------------------------------------------------+

void compile(FILE *source_code) {
  // note: this function closes the source code file
  // since we use global state, this should be called only once!
  // TODO: stop using global state
  ExprCall *program = parse(source_code);
  fclose(source_code); // we are done reading the file...
  program->show();
  std::cout << "\n parsing complete, compiling...\n";
  prefill_builtins();
  llvm::Function *main_fn = vi_get_fn(program->codegen()); // generate code
}



//>-----------------------------------------------------------+
//>     Main                                                  |
//>-----------------------------------------------------------+

int main(int argc, char **argv) {
  if (argc < 2) {
    std::cout << "please specify a file name to compile\n";
    return 0;
  }
  FILE *fp = fopen(argv[1], "r");
  if (fp == NULL) {
    std::cout << "invalid file\n";
    return 0;
  }
  compile(fp); // convert fp to llvm ir, and close the file
  // output the ir to a file
  if (argc == 2) {
    TheModule.print(llvm::errs(), nullptr);
  } else {
    char *message = NULL;
    LLVMPrintModuleToFile(llvm::wrap(&TheModule), argv[2], NULL);
  }
  return 0;
}

