#include "llvm/ADT/STLExtras.h"
#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>
#include <iostream>

// to compile: clang++ -g -O3 nts.cpp -o nts `llvm-config --cxxflags`



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
    if (str[*i] == '#') {
      do (*i)++;
      while (str[*i] != EOF && str[*i] != '\n' && str[*i] != '\r');
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
//>     AST Classes                                           |
//>-----------------------------------------------------------+

class ExprCall; // predeclaration

class Expr {
public:
  int kind = 0;
  bool quoted = false;
  Expr(int kind) : kind(kind) {}
  virtual ~Expr() {}
  virtual void show() {}
  virtual ExprCall *make_iter(std::vector<ExprCall *> &curr_stack) {
    std::cout << "error: did not expect to see a '[' here\n";
    exit(0);
    return NULL;
  }
  //virtual Value *codegen() = 0;
};

class ExprInt : public Expr {
public:
  int val;
  ExprInt(int val) : val(val), Expr(1) {}
  void show() {std::cout << " " << val << " ";}
  //virtual Value *codegen();
};

class ExprIden : public Expr {
public:
  std::string name;
  ExprIden(const std::string &name) : name(name), Expr(2) {}
  void show() {
    if (quoted)
      std::cout << " '" << name << " ";
    else
      std::cout << " " << name << " ";
  }
  //virtual Value *codegen();
};

class ExprCall : public Expr {
public:
  std::vector<Expr*> elems;
  ExprCall() : Expr(3) {}
  void show() {
    if (quoted)
      std::cout << " '( ";
    else
      std::cout << " ( ";
    for (Expr *expr : elems) expr->show();
    std::cout << " )";
  }
  ExprCall *make_iter(std::vector<ExprCall*> &curr_stack) {
    ExprCall *ans = new ExprCall;
    ans->elems.push_back(new ExprIden("for"));
    ExprCall *itervars = new ExprCall();
    curr_stack.push_back(itervars);
    ans->elems.push_back(itervars);
    ans->elems.push_back(this);
    return ans;
  }
  //virtual Value *codegen();
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
  ExprCall *program = new ExprCall();
  program->elems.push_back(new ExprIden("do"));
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
        tmp_expr = new ExprCall();
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
        curr_stack.back()->elems.push_back(new ExprIden(iden_str));
        break;
      case tok_int:
        curr_stack.back()->elems.push_back(new ExprInt(int_val));
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

/*static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;
static std::map<std::string, Value *> NamedValues;*/



//>-----------------------------------------------------------+
//>     Main                                                  |
//>-----------------------------------------------------------+

int main() {
  const std::string test_str = " ( 123 hello 789 - -4 -dqqq 'nil '(quoted list)[with iteration])[]\n   # stuff \n   # $$#$@ \n (+ 2 3 (+ i j))[i j] ";
  ExprCall *program = parse(test_str);
  program->show();
  return 0;
}

