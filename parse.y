%{

/* pars1.y    Pascal Parser      Gordon S. Novak Jr.  ; 30 Jul 13   */

/* Copyright (c) 2013 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/* 14 Feb 01; 01 Oct 04; 02 Mar 07; 27 Feb 08; 24 Jul 09; 02 Aug 12 */

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

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"
#include "pprint.h"

#define YYSTYPE TOKEN

TOKEN parseresult;

%}

%token IDENTIFIER STRING NUMBER

%token PLUS MINUS TIMES DIVIDE
%token ASSIGN EQ NE LT LE GE GT POINT DOT AND OR NOT DIV MOD IN

%token COMMA
%token SEMICOLON COLON LPAREN RPAREN LBRACKET RBRACKET DOTDOT

%token ARRAY BEGINBEGIN
%token CASE CONST DO DOWNTO ELSE END FILEFILE FOR FUNCTION GOTO IF LABEL NIL
%token OF PACKED PROCEDURE PROGRAM RECORD REPEAT SET THEN TO TYPE UNTIL
%token VAR WHILE WITH

%%

program    : PROGRAM IDENTIFIER LPAREN id_list RPAREN SEMICOLON lblock DOT   { parseresult = makeprogram($2, $4, $7); }
  statement  :  BEGINBEGIN statement endpart
                                       { $$ = makeprogn($1,cons($2, $3)); }
             |  IF expression THEN statement endif   { $$ = makeif($1, $2, $4, $5); }
             | FOR assign TO expression DO statement {$$  = makefor(1, $1, $2, $3, $4, $5, $6);}
             | funcall {$$ = $1;}
             |  assign {$$ = $1;}
             |  WHILE expression DO statement             { $$ = makewhile($1, $2, $3, $4); }
             |  REPEAT statement_list UNTIL expression    { $$ = makerepeat($1, $2, $3, $4); }
             |  GOTO NUMBER                               { $$ = dogoto($1, $2); }
             | label
             ;
assign :variable ASSIGN expression   { $$ = binop($2, $1, $3); }
              ;
cblock       :  CONST cdef_list tblock     { $$ = $3 ;}
             |  tblock
             ;
funcall    :  IDENTIFIER LPAREN expr_list RPAREN {$$ = makefuncall($2, $1, $3);}
             ;
endpart    :  SEMICOLON statement endpart    { $$ = cons($2, $3); }
            |  SEMICOLON END
            | END          {$$ = NULL;}
        ;

  variable     :  IDENTIFIER                            { $$ = $1; }
             |  variable DOT IDENTIFIER               { $$ = reducedot($1, $2, $3); }
             |  variable POINT                        { $$ = cons($2, $1); }
             |  variable LBRACKET expr_list RBRACKET  { $$ = arrayref($1, $2, $3, $4); }
             ;
  endif      :  ELSE statement                 { $$ = $2; }
             |  /* empty */                    { $$ = NULL; }
             ;
tdef     :  IDENTIFIER EQ type  { insttype($1, $3); }
             ;
block        :  BEGINBEGIN statement endpart { $$ = cons($2, $3); }
             ;

label        :  NUMBER COLON statement  { $$ = dolabel($1, $2, $3); }
             ;

statement_list:  statement                           { $$ = $1; }
              |  statement_list SEMICOLON statement  { $$ = cons($1, $3); }
              ;

field_list   :  fields                       { $$ = $1; }
             |  fields SEMICOLON field_list  { $$ = cons($1, $3); }
             ;
lblock       :  LABEL numlist SEMICOLON cblock  { instlabel($2); $$ = $4; }
             |  cblock                       { $$ = $1; }
             ;
 simple_expression : term   { $$ = $1; }
             | simple_expression plus_op term { $$ = binop($2, $1, $3); }
             | sign term     { $$ = unaryop($1, $2); }
             ;
vdef_list    :  vdef SEMICOLON              { $$ = $1; }
             |  vdef_list vdef SEMICOLON    { $$ = cons($1, $2); }
             ;
plus_op      :  PLUS | MINUS | OR;
             ;
vdef         :  id_list COLON type          { instvars($1, $3); }
             ;

times_op : TIMES | DIVIDE | DIV | MOD | AND
term         :  term times_op factor           { $$ = binop($2, $1, $3); }
             |  factor
             ;

id_list      :  IDENTIFIER                  { $$ = $1; }
             |  IDENTIFIER COMMA id_list    { $$ = cons($1, $3); }
             ;
constant :  IDENTIFIER              { $$ = $1; }
             | sign IDENTIFIER {$$ = $2;}
             |  sign NUMBER             { $$ = $2; }
             |  NUMBER                  { $$ = $1; }
             |  STRING                  { $$ = $1; }
             ;
cdef_list    :  cdef SEMICOLON              { $$ = $1; }
             |  cdef_list cdef SEMICOLON
             ;
cdef         :  IDENTIFIER EQ constant  { instconst($1, $3); }
             ;

numlist       :  NUMBER             { $$ = $1; }
             |  numlist COMMA NUMBER  { $$ = cons($1, $3); }
             ;

fields       :  id_list COLON type  { $$ = instfields($1, $3); }
             ;
simple_type  :  IDENTIFIER                       { $$ = $1; }
             |  LPAREN id_list RPAREN            { $$ = instenum($2); }
             |  constant DOTDOT constant { $$ = instdotdot($1, $2, $3); }
             ;
expr_list  : expression COMMA expr_list  {$$ = cons($1, $3);}
             | expression  {$$ = cons($1, NULL);}
             ;

sign         :  PLUS | MINUS  { $$ = $1; }

tblock       :  TYPE tdef_list vblock  { $$ = $3; }
             |  vblock
             ;

expression : expression compare_op simple_expression {$$ = binop($2, $1, $3);}
             | simple_expression  {$$ = $1;}
             ;
compare_op : EQ 
             | LT 
             | GT 
             | NE 
             | LE 
             | GE 
             | IN
             ;
unsigned_constant:  IDENTIFIER | NUMBER | NIL | STRING
              ;
 type      : simple_type  {$$ = $1;}
              |  ARRAY LBRACKET simple_type_list RBRACKET OF type { $$ = instarray($3, $6); }
             |  RECORD field_list END                   { $$ = instrec($1, $2); }
             |  POINT IDENTIFIER                        { $$ = instpoint($1, $2); }
             ;

simple_type_list :  simple_type                { $$ = $1; }
             |  simple_type COMMA simple_type_list  { $$ = cons($1, $3); }
             ;


vblock       :  VAR vdef_list vblock        { $$ = $3; }
             |  block
             ;

  
term         :  term multiply factor           { $$ = binop($2, $1, $3); }
             |  factor
             ;

tdef_list      :  tdef SEMICOLON          { $$ = $1; }
             |  tdef_list tdef SEMICOLON
             ;

multiply     :  TIMES | DIVIDE | DIV | MOD | AND
             ;
  


factor       :         unsigned_constant
       | variable
       | funcall
       | LPAREN expression RPAREN { $$ = $2; }
       | NOT factor
             ;

%%

int labelnumber = 0;

int labels[20];

TOKEN instdotdot(TOKEN lowtok, TOKEN dottok, TOKEN hightok) {
  int high  = hightok->intval;
  int low = lowtok->intval;
  return makesubrange(dottok, low, high);
}

TOKEN instfields(TOKEN idlist, TOKEN typetok) {
  TOKEN ret = idlist;
  while(idlist) {
    idlist -> symtype = searchins(typetok->stringval);;
    idlist = idlist-> link;
  }
 	return ret;
}

TOKEN instarray(TOKEN bounds, TOKEN typetok) {
  SYMBOL array = symalloc();
  TOKEN tokArray = talloc();
 	array->kind = ARRAYSYM;
  SYMBOL range = bounds -> symtype;
 	array->lowbound = range->lowbound;
 	array->highbound = range->highbound;

  array->datatype = bounds->link == NULL ? searchst(typetok->stringval) :symalloc();
 	if (bounds->link != NULL) {
    array->datatype = symalloc();
    array->datatype ->highbound = array->highbound;
 		array->datatype ->lowbound = array->lowbound;
 		array->datatype ->kind = ARRAYSYM;
    array->datatype ->datatype = searchst(typetok->stringval);
  }
  bounds = bounds -> link != NULL ? bounds->link : bounds;
 	array->size =  searchst(typetok->stringval)->size * (range->highbound - range->lowbound + 1);
 	tokArray->symtype = array;
 	return tokArray;
}


TOKEN instenum(TOKEN idlist) {
  int currentVal = 0;
  while(idlist) {
    TOKEN constVal = makeintc(currentVal);
    currentVal++;
    instconst(idlist, constVal);
    idlist = idlist -> link;
  }
  TOKEN input = talloc();
  int left = 0;
  int right = currentVal - 1;
  return makesubrange(input, 0, right); 
}

TOKEN instpoint(TOKEN tok, TOKEN typename) {
  SYMBOL pointer = symalloc();
  pointer->kind = POINTERSYM;
  pointer->datatype = searchins(typename->stringval);
  pointer -> size = basicsizes[POINTER];
  pointer -> basicdt = POINTER;
  tok->symtype = pointer;
 	return tok;
}

TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement) {
 	TOKEN label = makelabel();
  label->link = makeif(tok, expr, statement, NULL);
  int val = labelnumber;
  TOKEN checkVal = statement->operands;
 	while(checkVal->link){
    checkVal = checkVal->link;
   }
 	checkVal->link = makegoto(val - 1);
 	return makeprogn(tokb, label);
}

void instlabel(TOKEN num) {
    labelnumber++;
    labels[labelnumber] = num->intval;
}

void insttype(TOKEN typename, TOKEN typetok) {
  SYMBOL symbol = searchins(typename->stringval);
  symbol->kind = TYPESYM;
  symbol->datatype = typetok->symtype;
  int tokSize = typetok->symtype->size;
  symbol -> size = symbol->datatype->kind != RECORDSYM ? alignsize(symbol -> datatype) : tokSize;
}

TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {
  SYMBOL record =  var->symtype;
  int baseVal = 0;
  int ofVal = 0;
 	if (var->whichval == AREFOP) {     
     for (int i = 0; i < 3; i++) {
   	  record =record->datatype;
     }
 	} else {
    SYMBOL ptr = searchst(var->link->stringval);
    SYMBOL recordCheck =  var->link->whichval != AREFOP ? ptr-> datatype : var->link->symtype->datatype;
    for (int i = 0; i < 4; i++){
      recordCheck = recordCheck -> datatype;
    }
    record =  recordCheck;
    unaryop(var, var->link);
 	}
  while (record && strcmp(field->stringval, record->namestring)) {
    if (record->datatype->size == basicsizes[INTEGER && record->link->datatype->size == basicsizes[REAL]]) {
      record->datatype->size = basicsizes[REAL];
    }
 		ofVal += record->datatype->size;
     record = record -> link;
  }
  SYMBOL data_type = searchst(record->datatype->namestring);
  baseVal =data_type &&  !strcmp(field->stringval, record->namestring) ? data_type->basicdt :  baseVal;

  TOKEN array = makeop(AREFOP);
 	if (var->whichval == AREFOP) {
 		if (var->operands->link->tokentype == NUMBERTOK) {
 			var->operands->link->intval += ofVal;
    }
    array = var;
    array->basicdt = baseVal;
 	} else {
    TOKEN off_tok = makeintc(ofVal);
 		array = makearef(var, off_tok, dot);
 		array->basicdt = baseVal;
 		array->whichval = AREFOP;
 		array->symtype = record;
 	}
 	return array;
}

TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement) {
 	int index = labelnumber;
  tok = makelabel();
 	tok->link = statement;
  TOKEN temp = talloc();
  labels[labelnumber] = labeltok->intval;
  while (index){
        if (labels[index] == labeltok->intval) {
          TOKEN ret = makelabel();
          ret -> link = statement;
          ret -> operands = labeltok;//see if make more efficnet
        } 
        index--;
  }
   TOKEN ret = makeprogn(temp, tok);
 	return ret;
}

TOKEN makearef(TOKEN var, TOKEN off, TOKEN tok) {
  var->link = off;
 	TOKEN referenceVal = tok;
  referenceVal = referenceVal != NULL ? referenceVal : makeop(AREFOP);
  unaryop(referenceVal, var);
  referenceVal->tokentype = OPERATOR;
 	referenceVal->whichval = AREFOP;
 	return referenceVal;
}

TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements) {
    TOKEN nameProg = talloc();
    TOKEN statementProg = talloc();
    TOKEN prog  = makeop(PROGRAMOP);
    makeprogn(nameProg, args);
    unaryop(prog, name);
    makeprogn(statementProg, statements);
    cons(nameProg, statementProg);
    cons(name, nameProg);
    return prog;
}

void instvars(TOKEN idlist, TOKEN typetok) {
  while(idlist) {
    SYMBOL symbolCheck = insertsym(idlist->stringval);
		symbolCheck->kind = VARSYM;
    int typesSym = typetok->symtype == NULL;
    symbolCheck->datatype  = typesSym ? searchins(typetok->stringval) : typetok->symtype;	
    SYMBOL data = symbolCheck->datatype;	
    symbolCheck->basicdt = data->basicdt;
		symbolCheck->size = data->size;
    blockoffs[symbolCheck->blocklevel] +=  (!(symbolCheck->size < 16)) ? blockoffs[symbolCheck->blocklevel] % 16 : 0;
		symbolCheck->blocklevel = 1;
    int off =  blockoffs[1];
		symbolCheck->offset = off;
		blockoffs[1] += symbolCheck->size;
    idlist = idlist->link;
  }
}

TOKEN makesubrange(TOKEN tok, int low, int high) {
 	SYMBOL subrange = symalloc();
 	subrange->kind = SUBRANGE;
  subrange->lowbound = low;
 	subrange->highbound = high;
  subrange -> size = 4;
  tok->symtype = subrange;
 	return tok;
}


TOKEN instrec(TOKEN rectok, TOKEN argstok) {
  SYMBOL record = symalloc();
  record->kind = RECORDSYM;
 	record->datatype = makesym(argstok->stringval);
 	int size = 0;
  if ((argstok->symtype != NULL)) {
    size += argstok->symtype->size;
 		record->datatype->datatype = argstok->symtype;
 	}
   SYMBOL val = record->datatype;
 	while (argstok -> link) {
    argstok = argstok->link;
 		val->link = makesym(argstok->stringval);
     val = val->link;
    size += argstok->symtype != NULL ? argstok->symtype->size : 0;
 		if (argstok->symtype != NULL) {
 			val->datatype = argstok->symtype;
 		}
 	}
 	record->size = wordaddress(size, 16);
 	rectok->symtype = record;
 	return rectok;
}

void instconst(TOKEN idtok, TOKEN consttok) {
	  SYMBOL symbolVal = insertsym(idtok->stringval);
  	symbolVal->basicdt = consttok->basicdt;
	  symbolVal->kind = CONSTSYM;
    int switchCheck = consttok->basicdt;
    switch(switchCheck) {
      case INTEGER:
        symbolVal->constval.intnum = consttok->intval;
        break;
      case STRINGTYPE:
        strncpy(symbolVal->constval.stringconst, consttok->stringval, 16);
        break;
      case REAL:
        symbolVal->constval.realnum = consttok->realval;
        break;
    }
}

TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb) {
   tok = makeintc(0);
 	SYMBOL tempVal = searchst(arr->stringval) -> datatype;
 	SYMBOL recordVal = tempVal->datatype->datatype;
 	if (subs->tokentype == NUMBERTOK) {
 		tokb = makeintc(recordVal->size * (subs->intval - 1));
 		tok  = makeop(AREFOP);
    unaryop(tok, arr);
    cons(arr, tokb);
 		tok->symtype = tempVal;
 	} else if (subs->tokentype == IDENTIFIERTOK) {
    TOKEN addition = makeop(PLUSOP);
    unaryop(addition, tok);
    cons(arr, addition);
    TOKEN ret = makeop(AREFOP);
    unaryop(ret, arr);
     int intTok = tempVal->datatype->kind != ARRAYSYM ? tokb->intval = recordVal->size
      : tempVal->kind == ARRAYSYM ?  tokb->intval = recordVal->datatype->size * (recordVal->datatype->highbound - recordVal->datatype->lowbound + 1) : 0;
 		tokb = makeintc(intTok);
    int tokValues = tempVal->datatype->kind != ARRAYSYM ? -recordVal->size : 
      tempVal->kind == ARRAYSYM && searchst(subs->link->stringval)->kind == CONSTSYM ? 
        -(searchst(subs->link->stringval)->constval.intnum + 1)*recordVal->datatype->size : tok -> intval;
    tok -> intval = tokValues;
    subs-> link = tempVal->datatype->kind == ARRAYSYM && tempVal->kind == ARRAYSYM ? NULL : subs-> link;
    tokb->link = subs;
 		TOKEN multiply = makeop(TIMESOP);
    unaryop(multiply, tokb);
    cons(tok, multiply);
 		ret->symtype = tempVal;
 		return ret;
 	}
 	return tok;
}

void symbol_tok(SYMBOL symbolVal, TOKEN tok){
	tok->basicdt = symbolVal->basicdt;
  if (symbolVal->kind == CONSTSYM && symbolVal->basicdt == INTEGER ) {
    tok->tokentype  = NUMBERTOK;
    tok -> intval = symbolVal->constval.intnum;
  } else if (symbolVal->kind == CONSTSYM && symbolVal->basicdt == REAL) {
    tok->tokentype  = NUMBERTOK;
    tok -> realval = symbolVal->constval.realnum;
  }
}

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs) {
  int lhsReal = lhs->basicdt == REAL;
  int rhsInteger =  rhs->basicdt == INTEGER;
  int lhsInteger = lhs -> basicdt == INTEGER;
  int rhsReal = rhs ->basicdt == REAL;
  int assignCheck = op->whichval == ASSIGNOP;
  if (rhs->whichval == NIL - RESERVED_BIAS && rhs->tokentype == RESERVED) {
			rhs = makeintc(0);
  }
	if (rhs->stringval && searchst(rhs->stringval)) {
		  symbol_tok(searchst(rhs->stringval), rhs);
      rhsInteger =  rhs->basicdt == INTEGER;
      rhsReal = rhs ->basicdt == REAL;
  }
	if (lhs->stringval && searchst(lhs->stringval)) {
    symbol_tok(searchst(lhs->stringval), lhs);
      lhsInteger = lhs -> basicdt == INTEGER;
      lhsReal = lhs->basicdt == REAL;
  }

  op -> basicdt = lhsReal || rhsReal ? REAL : lhsInteger  && rhsInteger ? INTEGER : op -> basicdt;

	if ( lhsReal && rhsInteger) {
    rhs = makefloat(rhs);
  }
  if (assignCheck && lhsInteger && rhsReal) {
    rhs = makefix(rhs);
  }
  if (!assignCheck &&  lhsInteger && rhsReal ) {
    lhs  = makefloat(lhs);
  }
  cons(rhs, NULL);
  cons(lhs, rhs);
  unaryop(op, lhs);
  return op;
}



TOKEN dogoto(TOKEN tok, TOKEN labeltok){
  int index = labelnumber;
  int labVal = labeltok -> intval;
  while (index) {
 		if (labVal == labels[index - 1]) {
 			TOKEN ret = makegoto(index - 1);
 			return ret;
 		}
    index--;
  }
}

TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr, TOKEN tokc, TOKEN statement) {
  if (!sign) {
    return NULL;
  }
  TOKEN labelZero = makelabel();
  TOKEN lessThan = makeop(LEOP);
  TOKEN assignTok =makeop(ASSIGNOP);
  TOKEN programn = makeprogn(tokc, statement);
  TOKEN begStatement = talloc();
  begStatement->tokentype = IDENTIFIERTOK;
  strcpy(begStatement->stringval, asg->operands->stringval);
  TOKEN if_tok = binop(lessThan, begStatement, endexpr);
  labelZero->link = makeif(tok, if_tok, programn, NULL);
  asg->link = labelZero;
  statement->link = assignTok;
  asg->link = labelZero;
  cons(assignTok, makegoto(labelZero->operands->intval));
  TOKEN identificationInit = talloc();
  unaryop(assignTok, identificationInit);
  assignTok->operands = identificationInit;
  identificationInit->tokentype = IDENTIFIERTOK;
  identificationInit->link = makeplus(talloc(), makeintc(1), talloc());
  strcpy(identificationInit->stringval, asg->operands->stringval);
  identificationInit->link->operands->tokentype = IDENTIFIERTOK;
  strcpy(identificationInit->link->operands->stringval, asg->operands->stringval);
  return makeprogn(tokb, asg);
}


TOKEN makeplus(TOKEN lhs, TOKEN rhs, TOKEN tok) {
    TOKEN increment = makeop(PLUSOP);
    increment -> operands = lhs;
    lhs -> link = rhs;
    return increment;
}


TOKEN makeintc(int num) {
  TOKEN number = talloc();
  number -> tokentype = NUMBERTOK;
  number -> intval = num;
  number -> basicdt = INTEGER;
  return number;
}

TOKEN makelabel() {
  TOKEN ret = makeop(LABELOP);
  ret -> operands = makeintc(labelnumber);
  labelnumber++;
  return ret;
}

TOKEN makeop(int opnum) {
  TOKEN ret = talloc();
  ret->tokentype = OPERATOR;
  ret->whichval = opnum;
  return ret;
}

TOKEN makefloat(TOKEN tok) {
	if (tok->tokentype == NUMBERTOK) {
    tok->basicdt = REAL;
    tok->realval = tok->intval;
    return tok; 
    }
  TOKEN ret = makeop(FLOATOP);
	ret->operands = tok;
  return ret;
}

TOKEN makegoto(int label) {
  TOKEN gotoTok = talloc();
  gotoTok -> whichval = GOTOOP;
  gotoTok -> operands = makeintc(label);
  gotoTok -> tokentype = OPERATOR;
  return gotoTok;
}


TOKEN copytok(TOKEN origtok) {
  TOKEN ret = talloc();
  memcpy(ret, origtok, sizeof(TOKEN));
  return ret;
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

TOKEN makeprogn(TOKEN tok, TOKEN statements) {
  tok->whichval = PROGNOP;
  tok->tokentype = OPERATOR;
  tok->operands = statements;
  return tok;
}

TOKEN makefix(TOKEN tok) {
  TOKEN ret;
  if (tok -> tokentype == NUMBER) {
    tok -> intval = tok -> realval;
    tok->basicdt = INTEGER;
    ret = tok;
  } else {
    TOKEN correct = makeop(FIXOP);
    unaryop(correct, tok);
    ret = correct;
  }
  return ret;
}


TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) {
  TOKEN tokFunc = makeop(FUNCALLOP);
  tokFunc -> operands = fn;
  tokFunc -> operands -> link = args;
  tok = makeop(ASSIGNOP);

	if (strcmp(fn->stringval, "new")) {
    SYMBOL funStr = searchins(fn->stringval);
    cons (fn, args);
    tokFunc->basicdt = funStr->datatype->basicdt;
    tokFunc->operands = fn;
    return tokFunc;
	} 
  SYMBOL argVal = searchst(args->stringval);
  SYMBOL temp = argVal;
  for (int currentData = 0; currentData < 3; currentData++) {
    temp = temp -> datatype;
  }
  TOKEN tokSize = makeintc( temp->size);
  fn->link = tokSize;
  return binop(tok, args, tokFunc);
}

TOKEN unaryop(TOKEN op, TOKEN lhs) {
	op->operands = lhs;
	return op;
}

TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr) {
  TOKEN thenVal = talloc();
  TOKEN labelVal = makelabel();
  cons(labelVal, statements);
  while(statements -> link) {
    statements = statements -> link;
  }
	statements->link = makeif(tokb, expr, makeprogn(thenVal, NULL), makegoto(labelnumber - 1));
	return makeprogn(tok, labelVal);
}



int wordaddress(int n, int wordsize) {
  return ((n + wordsize - 1) / wordsize) * wordsize;
}

void yyerror (char const *s) {
  fprintf (stderr, "%s\n", s);
}

int main(void) { int res;
  initsyms();
  res = yyparse();
  printst();
  printf("yyparse result = %8d\n", res);
  ppexpr(parseresult);
}
