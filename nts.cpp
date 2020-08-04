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
//LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1

// to get llvm set up:
// https://clang.llvm.org/get_started.html # more up to date info
// https://llvm.org/docs/GettingStarted.html # tells about the -DLLVM_ENABLE_PROJECTS option
// note: The llvm library stuff accessible using c++ is called the "llvm c++ frontend".

// TODO list:
//  - make it so instead of codegen, fngen, typgen, we simply do a varinfogen, then typecheck tree structure, then perform final conversion to llvm IR (also macros fairly early on...)

//>-----------------------------------------------------------+
//>     Simple Error Handling                                 |
//>-----------------------------------------------------------+

int countlines(const std::string &str, int *pos) {
  // determine the line number of position pos in the string
  // assumes that 0 <= pos < length of str
  int ans = 1;
  for (int i = 0; i < *pos; i++) {
    if (str[i] == '\n')
      ans++;
  }
  return ans;
}

void error(const std::string msg, const std::string &str, int *pos) {
  std::cout << "Error on line " << countlines(str, pos) << ": " << msg << "\n";
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
  if (isalpha(c) || isdigit(c) || c == '+' || c == '-' ||
          c == '*' || c == '/' || c == '&' || c == '|' ||
          c == '?' || c == '=' || c == '<' || c == '>' || c == '!')
    return true;
  else
    return false;
}

static int gettok(std::string str, int *i) {
  // ignore whitespace and comments
  while (isspace(str[*i]) || str[*i] == '#') {
    if (str[*i] == '\n') line_no++; // '\n' counts as whitespace, so we can keep track of line numbers here
    if (str[*i] == '#') {
      do (*i)++; while (str[*i] != EOF && str[*i] != '\n' && str[*i] != '\r' && str[*i] != 0);
    } else {
      (*i)++;
    }
  }
  // check for end of string / file
  if (str[*i] == 0 || str[*i] == EOF) return tok_eof;
  // delimiters
  if (str[*i] == '(')  { (*i)++; return tok_opar; }
  if (str[*i] == ')')  { (*i)++; return tok_cpar; }
  if (str[*i] == '[')  { (*i)++; return tok_obrk; }
  if (str[*i] == ']')  { (*i)++; return tok_cbrk; }
  if (str[*i] == '\'') { (*i)++; return tok_quot; }
  // indentifier or digit
  if (isalnumsym(str[*i])) {
    std::string acc_str;
    int state = ls_start;
    do {
      switch (state) {
        case ls_start:
          if (str[*i] == '-')
            state = ls_minus;
          else if (isdigit(str[*i]))
            state = ls_numeral;
          else
            state = ls_ident;
          break;
        case ls_minus:
          if (isdigit(str[*i]))
            state = ls_numeral;
          else
            state = ls_ident;
          break;
      }
      acc_str += str[*i];
      (*i)++;
    } while (isalnumsym(str[*i]));
    switch (state) {
      case ls_minus:
      case ls_ident:
        iden_str = acc_str;
        return tok_iden;
      case ls_numeral:
        int_val = strtol(acc_str.c_str(), NULL, 0);
        if (errno != 0) error("invalid number literal", str, i);
        return tok_int;
    }
  }
  error("invalid character", str, i);
  return 0;
}


//>-----------------------------------------------------------+
//>     Type System                                           |
//>-----------------------------------------------------------+


enum TypCons { // ways to construct a typ
  tc_nil      = 0,
  tc_int      = 1,
  tc_fn       = -1,
  tc_tup      = -2,
};

typedef struct Typ {
  TypCons tc;
  struct Typ *t1;
  std::vector<struct Typ> *ts;
} Typ;

typedef struct VarInfo {
  Typ typ;
  llvm::Value *val;
  llvm::Function *fun;
} VarInfo;

VarInfo var_info_from_value(llvm::Value *val, Typ typ)      { return (VarInfo){typ, val,  NULL}; }
VarInfo var_info_from_function(llvm::Function *fn, Typ typ) { return (VarInfo){typ, NULL, fn  }; }

Typ *typ_alloc(Typ t) {
  Typ *ans = (Typ *)malloc(sizeof(Typ));
  *ans = t;
  return ans;
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
  virtual ExprCall *make_iter(std::vector<ExprCall *> &curr_stack) {
    std::cout << "error: did not expect to see a '[' here\n";
    exit(0);
    return NULL;
  }
  virtual std::string *get_iden() { return NULL; }
  virtual std::vector<Expr *> *get_elems() { return NULL; }
  virtual llvm::Value *codegen() = 0;
  virtual llvm::Function *fngen() = 0;
  virtual Typ typgen() = 0;
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
  virtual llvm::Value *codegen();
  virtual llvm::Function *fngen();
  virtual Typ typgen();
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
  virtual llvm::Value *codegen();
  virtual llvm::Function *fngen();
  virtual Typ typgen();
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
    ans->elems.push_back(new ExprIden("for", line));
    ExprCall *itervars = new ExprCall(line);
    curr_stack.push_back(itervars);
    ans->elems.push_back(itervars);
    ans->elems.push_back(this);
    return ans;
  }
  std::vector<Expr *> *get_elems() { return &elems; }
  virtual llvm::Value *codegen();
  virtual llvm::Function *fngen();
  virtual Typ typgen();
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

ExprCall *parse(const std::string inp_str) {
  int pos = 0;
  int tok = 0;
  // program is the thing we write to:
  ExprCall *program = new ExprCall(0);
  program->elems.push_back(new ExprIden("main_program_code", 0));
  // make stacks to keep track of program structure:
  std::vector<Delim> delim_stack; delim_stack.push_back(dl_file);
  std::vector<ExprCall*> curr_stack; curr_stack.push_back(program);
  // keep track of quoting
  bool quoting = false;
  // parse:
  while (tok != tok_eof) {
    tok = gettok(inp_str, &pos);
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
          error("did not expect to see ')' here", inp_str, &pos);
        curr_stack.pop_back();
        delim_stack.pop_back();
        break;
      case tok_obrk:
        tmp_expr = curr_stack.back()->elems.back()->make_iter(curr_stack);
        curr_stack[curr_stack.size() - 2]->elems.pop_back();
        curr_stack[curr_stack.size() - 2]->elems.push_back(tmp_expr);
        delim_stack.push_back(dl_brkt);
        break;
      case tok_cbrk:
        if (delim_stack.back() != dl_brkt)
          error("did not expect to see ']' here", inp_str, &pos);
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

llvm::Type *typ_conv(Typ t) {
  // convert Typs to llvm types
  return llvm::Type::getInt64Ty(TheContext);
  // TODO: be able to return non-integer types too
}

// prefill some named values:
void prefill_builtins() {
  // get the putchar function from C
  std::vector<llvm::Type *> args(1, llvm::Type::getInt64Ty(TheContext));
  std::vector<Typ> *argtyps = new std::vector<Typ>;
  argtyps->push_back((Typ){tc_int, NULL, NULL});
  llvm::FunctionType *FT = llvm::FunctionType::get(
    llvm::Type::getInt64Ty(TheContext), args, false);
  llvm::Function *F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, "putchar", TheModule);
  NamedValues->set("putchar", var_info_from_function(F, (Typ){tc_fn, typ_alloc((Typ){tc_int, NULL, NULL}), argtyps}));
  /*
  // 2 argument integer addition...
  std::vector<llvm::Type *> args(2, llvm::Type::getInt64Ty(TheContext));
  llvm::FunctionType *FT = llvm::FunctionType::get(
    llvm::Type::getInt64Ty(TheContext), args, false);
  llvm::Function *F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, "+", TheModule.get());
  int i = 0;
  for (auto &Arg : F->args())
    Arg.setName("x" + std::to_string(++i));
  
  llvm::BasicBlock *BB = llvm::BasicBlock::Create(TheContext, "entry", F);
  Builder.SetInsertPoint(BB);
  stackmap<std::string, std::pair<llvm::Value *, Typ>> nv(NamedValues); // new stackmap for arguments and local variables of this fn...
  NamedValues = &nv;
  for (auto &Arg : F->args())
    NamedValues->set(std::string(Arg.getName()), std::pair<llvm::Value *, Typ>(&Arg, (Typ){tc_int, NULL, NULL}));
  llvm::Value *retval = Builder.CreateAdd(
    NamedValues->at("x1").first,
    NamedValues->at("x2").first, "addtmp"); // TODO: look up what does addtmp mean (esp. tmp)
  Builder.CreateRet(retval);
  llvm::verifyFunction(*F);
  NamedValues = nv.pop(); // go back to normal
  // TODO: insert this nice new function into GlobalValues
  // TODO: lots more!!! (plus maybe addition should be inlined anyway :/) */
}

// codegen for the various expression types:


Typ ExprInt::typgen() {
  fail("can't interpret integer as a type");
  return (Typ){tc_nil, NULL, NULL};
}

llvm::Value *ExprInt::codegen() {
  return llvm::ConstantInt::get(TheContext, llvm::APInt(64, val, true));
}

llvm::Function *ExprInt::fngen() {
  fail("can't interpret integer as a function");
  return NULL;
}


Typ ExprIden::typgen() {
  if (name.compare("int") == 0) return (Typ){tc_int, NULL, NULL};
  if (name.compare("nil") == 0) return (Typ){tc_nil, NULL, NULL};
  // TODO: lookup user defined types here, once those are a thing
  fail(name + " is not a valid type");
  return (Typ){tc_nil, NULL, NULL};
}

llvm::Value *ExprIden::codegen() {
  if (NamedValues->has(name)) {
    VarInfo var_info = NamedValues->at(name);
    if (var_info.typ.tc == tc_fn) {
      fail("did not expect a function here!");
      return NULL;
    }
    return var_info.val;
  }
  fail("variable " + name + " is not defined here");
  return NULL;
}

llvm::Function *ExprIden::fngen() {
  if (NamedValues->has(name)) {
    VarInfo var_info = NamedValues->at(name);
    if (var_info.typ.tc != tc_fn) {
      fail(name + " is not a function");
      return NULL;
    }
    return var_info.fun;
  }
  fail("variable " + name + " is not defined here");
  return NULL;
}


Typ ExprCall::typgen() {
  if (elems[0]->get_iden()->compare("->") == 0) {
    // TODO: get typs of arguments...
    return (Typ){tc_fn, typ_alloc(elems[2]->typgen()), NULL};
  }
  fail("expression does not describe a type");
  return (Typ){tc_nil, NULL, NULL};
}

llvm::Value *ExprCall::codegen() {
  // TODO: special handling for for loops, def, <-, lambda, tensors, +, -, *, /, etc.
  int size = elems.size();
  if (size == 0) return NULL; // () yields nil (or something...)
  std::string *iden = elems[0]->get_iden();
  if (iden != NULL) { // check for and handle builtins...
    // TODO: assertions for argument number and structure for builtins
    if (iden->compare("+") == 0) { // handle addition
      return Builder.CreateAdd(
        elems[1]->codegen(),
        elems[2]->codegen(), "addtmp");
    }
    if (iden->compare("*") == 0) { // handle multiplication
      return Builder.CreateMul(
        elems[1]->codegen(),
        elems[2]->codegen(), "multmp");
    }
    if (iden->compare("def") == 0) {
      int i;
      // prepare signature
      Typ rettyp = elems[1]->typgen();
      std::string *fnname = elems[2]->get_iden();
      std::vector<Expr *> *arglist = elems[3]->get_elems();
      int arg_num = arglist->size() / 2;
      std::vector<Typ> *argtyps = new std::vector<Typ>;
      std::vector<llvm::Type *> arg_ltypes;
      std::vector<std::string> argnames;
      for (i = 0; i < arg_num; i++) {
        argtyps->push_back(arglist->at(2*i)->typgen());
        arg_ltypes.push_back(typ_conv(argtyps->back()));
        std::string *argnm = arglist->at(2*i + 1)->get_iden();
        if (argnm == NULL) fail("parameter names must be identifiers, not numbers or calls");
        argnames.push_back(argnm->substr());
      }
      llvm::FunctionType *FT = llvm::FunctionType::get(
        typ_conv(rettyp), arg_ltypes, false);
      llvm::Function *F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, *fnname, TheModule);
      i = 0;
      for (auto &Arg : F->args())
        Arg.setName(argnames[i++]);
      // set up fn args and body
      llvm::BasicBlock *BB = llvm::BasicBlock::Create(TheContext, "entry", F);
      Builder.SetInsertPoint(BB);
      stackmap<std::string, VarInfo> nv(NamedValues); // new stackmap for arguments and local variables of this fn...
      NamedValues = &nv;
      i = 0;
      for (auto &Arg : F->args())
        NamedValues->set(std::string(Arg.getName()), var_info_from_value(&Arg, (*argtyps)[i++]));
      // define body
      llvm::Value *retval = elems[4]->codegen();
      // cleanup
      Builder.CreateRet(retval);
      llvm::verifyFunction(*F);
      NamedValues = nv.pop(); // go back to normal
      // add function to list of defined values
      NamedValues->set(*fnname, var_info_from_function(F, (Typ){tc_fn, typ_alloc((Typ){tc_int, NULL, NULL}), argtyps})); // TODO: return things other than integers
      return NULL; // defining a fn yields nil
    }
    //if (iden->compare("print") == 0) {
    //  std::cout << "putc: " << TheModule.getFunction("puts") << "\n"; // TODO: this broken
    //}
  }
  // Case: user defined function
  llvm::Function *func = elems[0]->fngen();
  std::vector<VarInfo> args;
  args.reserve(size);
  for (int i = 1; i < size; i++) {
    args.push_back(var_info_from_value(elems[i]->codegen(), (Typ){tc_int, NULL, NULL})); // TODO: taking non-ints as args not supported yet
  }
  // TODO: check argument types and counts
  std::vector<llvm::Value *> args_llvm;
  for (int i = 1; i < size; i++) {
    args_llvm.push_back(args[i-1].val);
  }
  return Builder.CreateCall(func, args_llvm, "calltmp");
}

llvm::Function *ExprCall::fngen() {
  int size = elems.size();
  if (size == 0) return NULL; // () yields nil (or something...)
  std::string *iden = elems[0]->get_iden();
  if (iden != NULL) { // check for and handle builtins...
    if (iden->compare("main_program_code") == 0) {
      llvm::Type *rettyp = llvm::Type::getInt64Ty(TheContext);
      std::vector<llvm::Type *> argtyps; // this will stay empty
      llvm::FunctionType *FT = llvm::FunctionType::get(
        rettyp, argtyps, false);
      llvm::Function *F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage, "main", TheModule);
      llvm::BasicBlock *BB = llvm::BasicBlock::Create(TheContext, "entry2", F);
      Builder.SetInsertPoint(BB);
      llvm::Value *retval;
      for (int i = 1; i < size; i++) {
        retval = elems[i]->codegen();
        Builder.SetInsertPoint(BB);
      }
      retval = llvm::ConstantInt::get(TheContext, llvm::APInt(64, 0, true));
      Builder.CreateRet(retval);
      llvm::verifyFunction(*F);
      return F;
    }
    // TODO: lambda expressions, etc
  }
  fail("can't interpret this as a function!");
  return NULL;
}

// TODO: type checking...


//>-----------------------------------------------------------+
//>     Main                                                  |
//>-----------------------------------------------------------+

int main() {
  //const std::string test_str = " ( 123 hello 789 - -4 -dqqq 'nil '(quoted list)[with iteration])[]\n   # stuff \n   # $$#$@ \n (+ 2 3 (+ i j))[i j] "; // test string for parsing
  const std::string test_str = "(def int affine (int x int y) (+ x (* 4 y)))\n(putchar 33)#(affine -3 9))"; // very simple test string
  ExprCall *program = parse(test_str);
  program->show();
  std::cout << "\n parsing complete, compiling...\n";
  prefill_builtins();
  llvm::Function *main_fn = program->fngen(); // generate code
  TheModule.print(llvm::errs(), nullptr);
  // TheModule->print(llvm::errs(), NULL); // causes segfault right now, pls implement more stuff
  return 0;
}

