%{     /* pars1.y    Pascal Parser      Gordon S. Novak Jr.  ; 25 Jul 19   */

/* Copyright (c) 2019 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/* 14 Feb 01; 01 Oct 04; 02 Mar 07; 27 Feb 08; 24 Jul 09; 02 Aug 12 */
/* 30 Jul 13 */

/*
; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.
; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.
; You should have received a copy of the GNU General Public License
; along with this program; if not, see <http://www.gnu.org/licenses/>.
  */


/* NOTE:   Copy your lexan.l lexical analyzer to this directory.      */

       /* To use:
                     make pars1y              has 1 shift/reduce conflict
                     pars1y                   execute the parser
                     i:=j .
                     ^D                       control-D to end input
                     pars1y                   execute the parser
                     begin i:=j; if i+j then x:=a+b*c else x:=a*b+c; k:=i end.
                     ^D
                     pars1y                   execute the parser
                     if x+y then if y+z then i:=j else k:=2.
                     ^D
           You may copy pars1.y to be parse.y and extend it for your
           assignment.  Then use   make parser   as above.
        */

        /* Yacc reports 1 shift/reduce conflict, due to the ELSE part of
           the IF statement, but Yacc's default resolves it in the right way.*/

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"
#include "pprint.h"

			/* define the type of the Yacc stack element to be TOKEN */

#define YYSTYPE TOKEN

TOKEN parseresult;

%}

/* Order of tokens corresponds to tokendefs.c; do not change */

%token IDENTIFIER STRING NUMBER   /* token types */

%token PLUS MINUS TIMES DIVIDE    /* Operators */
%token ASSIGN EQ NE LT LE GE GT POINT DOT AND OR NOT DIV MOD IN

%token COMMA                      /* Delimiters */
%token SEMICOLON COLON LPAREN RPAREN LBRACKET RBRACKET DOTDOT

%token ARRAY BEGINBEGIN           /* Lex uses BEGIN */
%token CASE CONST DO DOWNTO ELSE END FILEFILE FOR FUNCTION GOTO IF LABEL NIL
%token OF PACKED PROCEDURE PROGRAM RECORD REPEAT SET THEN TO TYPE UNTIL
%token VAR WHILE WITH

%%

program      : PROGRAM IDENTIFIER LPAREN id_list RPAREN SEMICOLON lblock DOT   { parseresult = makeprogram($2, $4, $7); }
statement    :  BEGINBEGIN statement endpart
                                       { $$ = makeprogn($1,cons($2, $3)); }
             |  IF expression THEN statement endif   { $$ = makeif($1, $2, $4, $5); }
             | FOR assign TO expression DO statement {$$  = makefor(1, $1, $2, $3, $4, $5, $6);}
             | funcall {$$ = $1;}
             |  assign {$$ = $1;}
             |  WHILE expression DO statement             { $$ = makewhile($1, $2, $3,$4); }
             |  REPEAT statements UNTIL expression    { $$ = makerepeat($1, $2, $3, $4); }
             |  GOTO NUMBER                               { $$ = dogoto($1, $2); }
             | label
             ;
statements   :  statement                           { $$ = $1; }
             |  statements SEMICOLON statement  { $$ = cons($1, $3); }
             ;
assign       :  variable ASSIGN expression   { $$ = binop($2, $1, $3); }
             ;
arg_list     :  fields                       { $$ = $1; }
             |  fields SEMICOLON arg_list  { $$ = cons($1, $3); }
             ;
funcall      :  IDENTIFIER LPAREN expressions RPAREN {$$ = makefuncall($2, $1, $3);}
             ;
endpart      :  SEMICOLON statement endpart    { $$ = cons($2, $3); }
             |  SEMICOLON END
             |  END          {$$ = NULL;}
             ;

variable     :  IDENTIFIER                            { $$ = $1; }
             |  variable DOT IDENTIFIER               { $$ = reducedot($1, $2, $3); }
             |  variable POINT                        { $$ = cons($2, $1); }
             |  variable LBRACKET expressions RBRACKET  { $$ = arrayref($1, $2, $3, $4); }
             ;
endif        :  ELSE statement                 { $$ = $2; }
             |  /* empty */                    { $$ = NULL; }
             ;
block        :  BEGINBEGIN statement endpart { $$ = cons($2, $3); }
             ;
lblock       :  LABEL numlist SEMICOLON cblock  { instlabel($2); $$ = $4; }
             |  cblock                       { $$ = $1; }
             ;
cblock       :  CONST cdef_list tblock     { $$ = $3 ;}
             |  tblock
             ;
tblock       :  TYPE tdefs vblock  { $$ = $3; }
             |  vblock
             ;
label        :  NUMBER COLON statement  { $$ = dolabel($1, $2, $3); }
             ;
sExpr        :  term   { $$ = $1; }
             |  sExpr addOperator term { $$ = binop($2, $1, $3); }
             |  sign term     { $$ = unaryop($1, $2); }
             ;
expression   :  expression compare_op sExpr {$$ = binop($2, $1, $3);}
             |  sExpr  {$$ = $1;}
             ;             
expressions  :  expression COMMA expressions  {$$ = cons($1, $3);}
             |  expression  {$$ = cons($1, NULL);}
             ;
vdef         :  id_list COLON type          { instvars($1, $3); }
             ;
vdef_list    :  vdef SEMICOLON              { $$ = $1; }
             |  vdef_list vdef SEMICOLON    { $$ = cons($1, $2); }
             ;
cdef_list    :  cdef SEMICOLON              { $$ = $1; }
             |  cdef_list cdef SEMICOLON
             ;
id_list      :  IDENTIFIER                  { $$ = $1; }
             |  IDENTIFIER COMMA id_list    { $$ = cons($1, $3); }
             ;
sList        :  sType                { $$ = $1; }
             |  sType COMMA sList  { $$ = cons($1, $3); }
             ;
cdef         :  IDENTIFIER EQ constant  { instconst($1, $3); }
             ;
addOperator  :  PLUS | MINUS | OR;
             ;
operator     :  TIMES | DIVIDE | DIV | MOD | AND
term         :  term operator var           { $$ = binop($2, $1, $3); }
             |  var
             ;
sign         :  PLUS | MINUS  { $$ = $1; }
constant     :  IDENTIFIER              { $$ = $1; }
             |  sign IDENTIFIER {$$ = $2;}
             |  sign NUMBER             { $$ = $2; }
             |  NUMBER                  { $$ = $1; }
             |  STRING                  { $$ = $1; }
             ;
numlist      :  NUMBER             { $$ = $1; }
             |  numlist COMMA NUMBER  { $$ = cons($1, $3); }
             ;
fields       :  id_list COLON type  { $$ = instfields($1, $3); }
             ;
sType        :  IDENTIFIER                       { $$ = $1; }
             |  LPAREN id_list RPAREN            { $$ = instenum($2); }
             |  constant DOTDOT constant { $$ = instdotdot($1, $2, $3); }
             ;
type         : sType  {$$ = $1;}
             |  ARRAY LBRACKET sList RBRACKET OF type { $$ = instarray($3, $6); }
             |  RECORD arg_list END                   { $$ = instrec($1, $2); }
             |  POINT IDENTIFIER                        { $$ = instpoint($1, $2); }
             ;
compare_op   :  EQ 
             |  LT 
             |  GT 
             |  NE 
             |  LE 
             |  GE 
             |  IN
             ;
prod         :  TIMES | DIVIDE | DIV | MOD | AND
             ;
u_const      :  IDENTIFIER | NUMBER | NIL | STRING
             ;
vblock       :  VAR vdef_list vblock        { $$ = $3; }
             |  block
             ;
tdef         :  IDENTIFIER EQ type  { insttype($1, $3); }
             ;
tdefs        :  tdef SEMICOLON          { $$ = $1; }
             |  tdefs tdef SEMICOLON
             ;
var          :  u_const
             |  variable
             |  funcall
             |  LPAREN expression RPAREN { $$ = $2; }
             |  NOT var
             ;

%%

int labelnumber = 0;  /* sequential counter for internal label numbers */

   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */


int labelList[40];

TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement) {
 	int idx = labelnumber;
  tok = makelabel();
 	tok->link = statement;
  TOKEN sym = talloc();
  labelList[labelnumber] = labeltok->intval;
  int count = 0;
  while (count != idx){
    if (labeltok->intval == labelList[idx]) {
      TOKEN ret = makelabel();
      ret -> link = statement;
      ret -> operands = labeltok;//see if make more efficnet
    } 
    count++;
  }
 	return makeprogn(sym, tok);
}

TOKEN makearef(TOKEN var, TOKEN off, TOKEN tok) {
  var->link = off;
 	TOKEN val = tok;
  val = val != NULL ? val : makeop(AREFOP);
  unaryop(val, var);
  val->tokentype = OPERATOR;
 	val->whichval = AREFOP;
 	return val;
}

/* makeprogram makes the tree structures for the top-level program */
TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements) {
  TOKEN progNameTok = talloc();
  TOKEN progTok  = makeop(PROGRAMOP);
  progTok -> operands = name;
  progNameTok = makeprogn(progNameTok, args);
  name -> link = progNameTok;
  progNameTok -> link = statements;
  return progTok;  
}

void instvars(TOKEN idlist, TOKEN typetok) {
  SYMBOL symbol;
  while(idlist != NULL) {
    symbol = insertsym(idlist->stringval);
    int symbolType = typetok->symtype == NULL;
    if(symbolType){
      symbol->datatype = searchins(typetok->stringval);
    } else {
      symbol->datatype = typetok->symtype;
    }
		symbol->kind = VARSYM;
    SYMBOL val = symbol->datatype;	
    symbol->basicdt = val->basicdt;
		symbol->size = val->size;
    blockoffs[symbol->blocklevel] +=  (!(symbol->size < 16)) ? blockoffs[symbol->blocklevel] % 16 : 0;
		symbol->blocklevel = 1;
    int off =  blockoffs[1];
		symbol->offset = off;
		blockoffs[1] += symbol->size;
    idlist = idlist->link;
  }
}
//new
void symtotok(SYMBOL symbolVal, TOKEN tok){
  tok->basicdt = symbolVal->basicdt;
  if (symbolVal->kind == CONSTSYM && symbolVal->basicdt == INTEGER ) {
    if (symbolVal->basicdt == INTEGER){
      tok->tokentype  = NUMBERTOK;
      tok -> intval = symbolVal->constval.intnum;
    } else if (symbolVal->basicdt == REAL){
      tok->tokentype  = NUMBERTOK;
      tok -> realval = symbolVal->constval.realnum;
    }
  }
}

TOKEN instdotdot(TOKEN lowtok, TOKEN dottok, TOKEN hightok) {

  SYMBOL subrange = symalloc();
  subrange->kind = SUBRANGE;
  subrange->lowbound = lowtok->intval;
  subrange->highbound = hightok->intval;
  subrange -> size = 4;
  dottok->symtype = subrange;
  return dottok;
}

TOKEN instfields(TOKEN idlist, TOKEN typetok) {
  TOKEN final = idlist;
  while(idlist != NULL) {
    idlist -> symtype = searchins(typetok->stringval);;
    idlist = idlist-> link;
  }
  return final;
}

TOKEN instarray(TOKEN bounds, TOKEN typetok) {
  SYMBOL list = symalloc();
  TOKEN tokenList = talloc();
  list->kind = ARRAYSYM;
  SYMBOL sym = bounds -> symtype;
  list->lowbound = sym->lowbound;
  list->highbound = sym->highbound;
  if (bounds->link == NULL) {
    list->datatype = searchst(typetok->stringval);
  } else {
    list->datatype = symalloc();
  }
  if (bounds->link) {
    list->datatype = symalloc();
    list->datatype ->lowbound = list->lowbound;
    list->datatype ->highbound = list->highbound;
    list->datatype ->kind = ARRAYSYM;
    list->datatype ->datatype = searchst(typetok->stringval);
  }
  bounds = bounds -> link != NULL ? bounds->link : bounds;
  list->size =  searchst(typetok->stringval)->size * (sym->highbound - sym->lowbound + 1);
  tokenList->symtype = list;
  return tokenList;
}


TOKEN instenum(TOKEN idlist) {
  int count = 0;
  while(idlist != NULL) {
    TOKEN constVal = makeintc(count);
    count++;
    instconst(idlist, constVal);
    idlist = idlist -> link;
  }
  TOKEN input = talloc();
  SYMBOL subrange = symalloc();
  subrange->kind = SUBRANGE;
  subrange->lowbound = 0;
  subrange->highbound = count - 1;
  subrange -> size = 4;
  input->symtype = subrange;
  return input;
}

TOKEN instpoint(TOKEN tok, TOKEN typename) {
  SYMBOL ptr = symalloc();
  ptr->kind = POINTERSYM;
  ptr->datatype = searchins(typename->stringval);
  ptr -> size = basicsizes[POINTER];
  ptr -> basicdt = POINTER;
  tok->symtype = ptr;
  return tok;
}

TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {
  SYMBOL data =  var->symtype;
  int initVal = 0;
  int offset = 0;
  if (var->whichval != AREFOP) {     
    SYMBOL pointer = searchst(var->link->stringval);
    SYMBOL recordCheck =  var->link->whichval != AREFOP ? pointer-> datatype : var->link->symtype->datatype;
    int count = 0;
    while (count<4) {
      recordCheck = recordCheck -> datatype;
    }
    data =  recordCheck;
    unaryop(var, var->link);     
  } else {
      int count = 0;
      while (count<3) {
        count += 1;
        data =data->datatype;
      }
  }
  while (data != NULL && strcmp(field->stringval, data->namestring)) {
    if (data->datatype->size == basicsizes[INTEGER && data->link->datatype->size == basicsizes[REAL]]) {
      data->datatype->size = basicsizes[REAL];
    }
    offset += data->datatype->size;
    data = data -> link;
  }
  SYMBOL data_type = searchst(data->datatype->namestring);
  initVal =data_type &&  !strcmp(field->stringval, data->namestring) ? data_type->basicdt :  initVal;

  TOKEN list = makeop(AREFOP);
  if (var->whichval == AREFOP) {
    if (var->operands->link->tokentype == NUMBERTOK) {
      var->operands->link->intval += offset;
      list = var;
      list->basicdt = initVal;
    } else {
      list = var;
      list->basicdt = initVal;
    }    
  } else {
    TOKEN off = makeintc(offset);
    var->link = off;
    TOKEN val = dot;
    val = val != NULL ? val : makeop(AREFOP);
    unaryop(val, var);
    val->tokentype = OPERATOR;
    val->whichval = AREFOP;
    return val;
  }
  return list;
}

TOKEN makewhile(TOKEN tok, TOKEN sExpr, TOKEN tokb, TOKEN statement) {
  TOKEN label = makelabel();
  label->link = makeif(tok, sExpr, statement, NULL);
  TOKEN val = statement->operands;
  while(val->link != NULL){
    val = val->link;
  }
  val->link = makegoto(labelnumber - 1);
  return makeprogn(tokb, label);
}

void instlabel(TOKEN num) {
    labelnumber++;
    labelList[labelnumber] = num->intval;
}

void insttype(TOKEN typename, TOKEN typetok) {
  SYMBOL symbol = searchins(typename->stringval);
  symbol->kind = TYPESYM;
  symbol->datatype = typetok->symtype;
  int length = typetok->symtype->size;
  if (symbol->datatype->kind == RECORDSYM) {
    symbol -> size = length;
  } else {
    symbol -> size = alignsize(symbol -> datatype);
  }
}



TOKEN instrec(TOKEN rectok, TOKEN argstok) {
  SYMBOL data = symalloc();
  data->kind = RECORDSYM;
 	data->datatype = makesym(argstok->stringval);
 	int length = 0;
  if ((argstok->symtype != NULL)) {
    length += argstok->symtype->size;
 		data->datatype->datatype = argstok->symtype;
 	}
   SYMBOL val = data->datatype;
 	while (argstok -> link) {
    argstok = argstok->link;
 		val->link = makesym(argstok->stringval);
    val = val->link;
    if (argstok->symtype != NULL){
      length +=  argstok->symtype->size;
      val->datatype = argstok->symtype;
    } 
 	}
 	data->size = wordaddress(length, 16);
 	rectok->symtype = data;
 	return rectok;
}

TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb) {  
  tok = makeintc(0);
 	SYMBOL val = searchst(arr->stringval) -> datatype;
 	SYMBOL data = val->datatype->datatype;
 	if (subs->tokentype == IDENTIFIERTOK) {
 		TOKEN sum = makeop(PLUSOP);
    unaryop(sum, tok); cons(arr, sum);
    TOKEN final = makeop(AREFOP);
    unaryop(final, arr);
    int intTok = 0;
    if (val->datatype->kind != ARRAYSYM) {
      intTok = tokb->intval = data->size;
    } else if(val->kind == ARRAYSYM) {
      int mult = data->datatype->highbound - data->datatype->lowbound + 1;
      int val = data->datatype->size * mult ;
      intTok = tokb->intval = val;
    }
    tokb = makeintc(intTok);
    int value = 0;
    if (val->datatype->kind != ARRAYSYM) {
      value = -data->size;
    } else {
      if (val->kind == ARRAYSYM && searchst(subs->link->stringval)->kind == CONSTSYM){
        int val = searchst(subs->link->stringval)->constval.intnum + 1;
        value = -(val)*data->datatype->size;
      } else {
        value = tok -> intval;
      }
    }
    tok -> intval = value;
    subs-> link = val->datatype->kind == ARRAYSYM && val->kind == ARRAYSYM ? NULL : subs-> link;
    tokb->link = subs;
    TOKEN prod = makeop(TIMESOP);
    unaryop(prod, tokb);
    cons(tok, prod);
    final->symtype = val;
    return final;
 	} else if (subs->tokentype == NUMBERTOK) {
    tok  = makeop(AREFOP);
    tokb = makeintc(data->size * (subs->intval - 1));
    unaryop(tok, arr);
    cons(arr, tokb);
    tok->symtype = val;
 	}
 	return tok;
}

void instconst(TOKEN idtok, TOKEN consttok) {
  SYMBOL symbolVal = insertsym(idtok->stringval);
	symbolVal->basicdt = consttok->basicdt;
  symbolVal->kind = CONSTSYM;
  int type = consttok->basicdt;
  if (type == INTEGER) {
    symbolVal->constval.intnum = consttok->intval;
  } else if (type == STRINGTYPE) {
    strncpy(symbolVal->constval.stringconst, consttok->stringval, 16);
  } else if (type == REAL){
    symbolVal->constval.realnum = consttok->realval;
  }
}

//new
void getSym(SYMBOL symbolVal, TOKEN tok){
  tok->basicdt = symbolVal->basicdt;
  if (symbolVal->kind == CONSTSYM)
    if (symbolVal->basicdt == INTEGER ) {
      tok -> intval = symbolVal->constval.intnum;
      tok->tokentype  = NUMBERTOK;
    } else if (symbolVal->basicdt == REAL){
      tok -> realval = symbolVal->constval.realnum;
      tok->tokentype  = NUMBERTOK;
    }
}


//new
TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs) {     
  int leftR = lhs-> basicdt == REAL;
  int rightInt =  rhs-> basicdt == INTEGER;
  int leftInt = lhs -> basicdt == INTEGER;
  int rightR = rhs -> basicdt == REAL;
  SYMBOL leftSymbol;
  SYMBOL rightSymbol;
  if (rhs->whichval == NIL - RESERVED_BIAS && rhs->tokentype == RESERVED) {
      rhs = makeintc(0);
      rhs->symtype = makesym("nil");
    }
  if (lhs->stringval != NULL){
    leftSymbol = searchst(lhs->stringval);
  }
  if (rhs->stringval != NULL){
    rightSymbol = searchst(rhs->stringval);
  }
  if (leftSymbol) {
    lhs->symentry = leftSymbol;
    getSym(leftSymbol, lhs);
    rightInt =  rhs->basicdt == INTEGER;
    rightR = rhs ->basicdt == REAL; 
  }
  if (rightSymbol) {
    rhs->symentry = rightSymbol;
    getSym(rightSymbol, rhs);
          leftInt = lhs -> basicdt == INTEGER;
      leftR = lhs->basicdt == REAL;
  }
  if (rhs->stringval && searchst(rhs->stringval)) {
      getSym(searchst(rhs->stringval), rhs);
      rightInt =  rhs->basicdt == INTEGER;
      rightR = rhs ->basicdt == REAL;
  }
  if (lhs->stringval && searchst(lhs->stringval)) {
      getSym(searchst(lhs->stringval), lhs);
      leftInt = lhs -> basicdt == INTEGER;
      leftR = lhs->basicdt == REAL;
  }
  op -> basicdt = leftR || rightR ? REAL : leftInt  && rightInt ? INTEGER : op -> basicdt;
  if ( leftR && rightInt) {
    rhs = makefloat(rhs);
  }
  if (op->whichval == ASSIGNOP && leftInt && rightR) {
    TOKEN sym;
    if (rhs -> tokentype == NUMBER) {
      rhs -> intval = rhs -> realval;
      rhs->basicdt = INTEGER;
      sym = rhs;
    } else {
      TOKEN correct = makeop(FIXOP);
      unaryop(correct, rhs);
      sym = correct;
    }
    rhs = sym;
  } else if (!op->whichval == ASSIGNOP &&  leftInt && rightR) {
    lhs  = makefloat(lhs);
  }
  cons(rhs, NULL);
  cons(lhs, rhs);
  unaryop(op, lhs);
  return op;
}

/*
TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs) {
  int lhsFloat = lhs->basicdt == REAL;
  int rhsInt =  rhs->basicdt == INTEGER;
  int lhsInt = lhs -> basicdt == INTEGER;
  int rhsFloat = rhs ->basicdt == REAL;
  int assignCheck = op->whichval == ASSIGNOP;
  if (rhs->whichval == NIL - RESERVED_BIAS && rhs->tokentype == RESERVED) {
			rhs = makeintc(0);
  }
	if (rhs->stringval && searchst(rhs->stringval)) {
    SYMBOL sym = searchst(rhs->stringval);
    rhs->basicdt = sym->basicdt;
    if (sym->kind == CONSTSYM && sym->basicdt == INTEGER ) {
      rhs->tokentype  = NUMBERTOK;
      rhs -> intval = sym->constval.intnum;
    } else if (sym->kind == CONSTSYM && sym->basicdt == REAL) {
      rhs->tokentype  = NUMBERTOK;
      rhs -> realval = sym->constval.realnum;
    }
    rhsInt =  rhs->basicdt == INTEGER;
    rhsFloat = rhs ->basicdt == REAL;
  }
	if (lhs->stringval && searchst(lhs->stringval)) {
    SYMBOL sym = searchst(lhs->stringval);
    lhs->basicdt = sym->basicdt;
    if (sym->kind == CONSTSYM && sym->basicdt == INTEGER ) {
      lhs->tokentype  = NUMBERTOK;
      lhs -> intval = sym->constval.intnum;
    } else if (sym->kind == CONSTSYM && sym->basicdt == REAL) {
      lhs->tokentype  = NUMBERTOK;
      lhs -> realval = sym->constval.realnum;
    }
    lhsInt = lhs -> basicdt == INTEGER;
    lhsFloat = lhs->basicdt == REAL;
  }
  if (lhsFloat || rhsFloat){
    op -> basicdt = REAL;
  } else if(lhsInt != NULL  && rhsInt != NULL) {
    op -> basicdt = INTEGER;
  }

	if ( lhsFloat && rhsInt) {
    rhs = makefloat(rhs);
  }
  if (assignCheck && lhsInt && rhsFloat) {
    TOKEN sym;
    if (rhs -> tokentype == NUMBER) {
      rhs -> intval = rhs -> realval;
      rhs->basicdt = INTEGER;
      sym = rhs;
    } else {
      TOKEN correct = makeop(FIXOP);
      unaryop(correct, rhs);
      sym = correct;
    }
    rhs = sym;
  }
  if (!assignCheck &&  lhsInt && rhsFloat ) {
    lhs  = makefloat(lhs);
  }
  cons(rhs, NULL);
  cons(lhs, rhs);
  unaryop(op, lhs);
  return op;
}
*/

TOKEN makefloat(TOKEN tok) {
	if (tok->tokentype == NUMBERTOK) {
    tok->basicdt = REAL;
    tok->realval = tok->intval;
    return tok; 
  }
  TOKEN sym = makeop(FLOATOP);
	sym->operands = tok;
  return sym;
}


TOKEN dogoto(TOKEN tok, TOKEN labeltok){
  int index = labelnumber;
  int labVal = labeltok -> intval;
  int count = 0;
  while (count < index) {
 		if (labVal == labelList[index - 1]) {
 			TOKEN ret = makegoto(index - 1);
 			return ret;
 		}
    count++;
  }
}

TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr, TOKEN tokc, TOKEN statement) {
  if (sign) {
    TOKEN label = makelabel();
    TOKEN tokenc =makeop(ASSIGNOP);
    TOKEN start = talloc();

    start->tokentype = IDENTIFIERTOK;
    strcpy(start->stringval, asg->operands->stringval);
    TOKEN if_tok = binop(makeop(LEOP), start, endexpr);
    label->link = makeif(tok, if_tok, makeprogn(tokc, statement), NULL);
    asg->link = label;
    statement->link = tokenc;
    asg->link = label;
    cons(tokenc, makegoto(label->operands->intval));
    TOKEN init = talloc();
    unaryop(tokenc, init);
    tokenc->operands = init;
    init->tokentype = IDENTIFIERTOK;
    init->link = makeplus(talloc(), makeintc(1), talloc());
    strcpy(init->stringval, asg->operands->stringval);
    init->link->operands->tokentype = IDENTIFIERTOK;
    strcpy(init->link->operands->stringval, asg->operands->stringval);
    return makeprogn(tokb, asg);
  } else {
    return NULL;
  }
}


TOKEN makeplus(TOKEN lhs, TOKEN rhs, TOKEN tok) {
    TOKEN increment = makeop(PLUSOP);
    increment -> operands = lhs;
    lhs -> link = rhs;
    return increment;
}


TOKEN makeintc(int num) {
  TOKEN intcTok = talloc();
  intcTok-> tokentype = NUMBERTOK;
  intcTok -> intval = num;
  intcTok -> basicdt = INTEGER;
  return intcTok;
}

TOKEN makelabel() {
  TOKEN labelTok = makeop(LABELOP);
  labelTok -> operands = makeintc(labelnumber);
  labelnumber++;
  return labelTok;
}

TOKEN makeop(int opnum) {
  TOKEN operatorTok = talloc();
  operatorTok -> tokentype = OPERATOR;
  operatorTok -> whichval = opnum;
  return operatorTok; 
}


TOKEN makegoto(int label) {
  TOKEN gotoTok = talloc();
  gotoTok -> whichval = GOTOOP;
  TOKEN intcTok = makeintc(label);
  gotoTok -> operands = intcTok;
  gotoTok -> tokentype = OPERATOR;
  return gotoTok;
}


TOKEN copytok(TOKEN origtok) {
  TOKEN sym = talloc();
  memcpy(sym, origtok, sizeof(TOKEN));
  return sym;
}

TOKEN cons(TOKEN item, TOKEN list) {
  item->link = list;
  return item;
}

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart) {
  tok->tokentype = OPERATOR;
  tok->whichval = IFOP;
  exp->link = thenpart;
  tok->operands = exp;
  if (elsepart != NULL) {
    elsepart->link = NULL;
    thenpart->link = elsepart;
  }
  return tok;
}

TOKEN makeprogn(TOKEN tok, TOKEN statements) 
{ tok->tokentype = OPERATOR;
  tok->whichval = PROGNOP;
  tok->operands = statements;
  return tok;
}

//new
TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) {
  TOKEN r = makeop(FUNCALLOP);
  if ( strcmp(fn->stringval, "new") == 0) {
    r->operands = fn;
    SYMBOL temp = searchst(args->stringval);
    temp = temp->datatype->datatype->datatype->datatype;
    cons(fn,  makeintc(temp->size));
    return binop(makeop(ASSIGNOP), args, r);  
  } else if ( strcmp(fn->stringval, "writeln") == 0 ) {
    if (args->tokentype != STRINGTOK) {
      if (args -> basicdt == REAL){
        strcpy(fn->stringval, "writelnf");
      } else {
        strcpy(fn->stringval, "writelni");
      }
    }
  }
  r->basicdt = searchins(fn->stringval)->datatype->basicdt; 
  cons(fn, args);
  unaryop(r, fn);
  return r;
}
/*
TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) {
  TOKEN funcallTok = makeop(FUNCALLOP);
  funcallTok -> operands = fn;
  funcallTok -> operands -> link = args;
  tok = makeop(ASSIGNOP);
	if (strcmp(fn->stringval, "new")) {
    cons (fn, args);
    funcallTok->basicdt = searchins(fn->stringval)->datatype->basicdt;
    funcallTok->operands = fn;
    return funcallTok;
	} 
  SYMBOL sym = searchst(args->stringval);
  for (int currentData = 0; currentData < 3; currentData++) {
    sym = sym -> datatype;
  }
  fn->link = makeintc( sym->size);
  return binop(tok, args, funcallTok);
}
*/

TOKEN unaryop(TOKEN op, TOKEN lhs) {
	op->operands = lhs;
	return op;
}

TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN sExpr) {
  TOKEN val = makelabel();
  cons(val, statements);
  while(statements -> link) {
    statements = statements -> link;
  }
  TOKEN temp = makegoto(labelnumber - 1);
	statements->link = makeif(tokb, sExpr, makeprogn(talloc(), NULL), temp);
	return makeprogn(tok, val);
}



int wordaddress(int n, int wordsize) 
{  return ((n + wordsize - 1) / wordsize) * wordsize; }

void yyerror (char const *s) 
{ fprintf (stderr, "%s\n", s); }

int main(void) {             /*  */
  int res;
  initsyms();
  res = yyparse();
  printstlevel(1);        /* to shorten, change to:  printstlevel(1);  */
  printf("yyparse result = %8d\n", res);
  if (DEBUG) dbugprinttok(parseresult);
  ppexpr(parseresult);      /* Pretty-print the result tree */
  /* uncomment following to call code generator. */
  /* 
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
  */
}
