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
#include "codegen.h"

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

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.
 */
int labelnumber = 0;  /* sequential counter for internal label numbers */
int labels[20];
   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */

//c
TOKEN cons(TOKEN item, TOKEN list) {             /* add item to front of list */
  item->link = list;
    return item;
  }

//c
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

//c
TOKEN dogoto(TOKEN tok, TOKEN labeltok) {
  int i = 0;
  int len = labeltok -> intval;
  int check = 1;
  while (check == 1){
    if (len == labels[i]){
      return makegoto(i-2);
      check = 0;
    }
    if (check == 0){
      break;
    } else {
      i++;
    }
  }
}

//c
TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement) {
 	int index = labelnumber;
  tok = makelabel();
 	tok->link = statement;
  TOKEN temp = talloc();
  labels[labelnumber] = labeltok->intval;

  for (int i = labeltok->intval - 1; i > 0; i--){
    if (labels[index] == labeltok->intval) {
      TOKEN ret = makelabel();
      ret -> link = statement;
      ret -> operands = labeltok;
    }    
  }
  TOKEN val = makeprogn(temp, tok);
 	return val;
}

//c
/* makefloat forces the item tok to be floating, by floating a constant
   or by inserting a FLOATOP operator */
TOKEN makefloat(TOKEN tok) {
  TOKEN result;
  if(tok->tokentype == NUMBERTOK) {
    tok->basicdt = REAL;
    tok->realval = (double) tok->intval;
    result = tok;
  } else {
    result = makeop(FLOATOP);
    result->operands = tok;
  }
  return result;
}

//c
/* makeop makes a new operator token with operator number opnum.
   Example:  makeop(FLOATOP)  */
TOKEN makeop(int opnum){
    TOKEN tok = talloc();
    tok->tokentype = OPERATOR;
    tok->whichval = opnum;
    return tok;
}

//c
/* makefix forces the item tok to be integer, by truncating a constant
   or by inserting a FIXOP operator */
TOKEN makefix(TOKEN tok) {
  if(tok->tokentype == NUMBERTOK) {
    tok->basicdt = INTEGER;
    tok->intval = (int) tok->realval;
    return tok;
  } else { 
    TOKEN fixop = makeop(FIXOP);
    fixop->operands = tok;
    return fixop;
  }
}

//check
TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb) {
	tok = makeintc(0);
 	SYMBOL val = searchst(arr->stringval) -> datatype;
 	SYMBOL recV = val->datatype->datatype;
 	if (subs->tokentype == NUMBERTOK) {
 		tokb = makeintc(recV->size * (subs->intval - 1));
 		tok  = makeop(AREFOP);
    unaryop(tok, arr);
    cons(arr, tokb);
 		tok->symtype = val;
 	} else if (subs->tokentype == IDENTIFIERTOK) {
    TOKEN addition = makeop(PLUSOP);
    unaryop(addition, tok);
    cons(arr, addition);
    TOKEN ret = makeop(AREFOP);
    unaryop(ret, arr);
    int intTok = val->datatype->kind != ARRAYSYM ? tokb->intval = recV->size
    : val->kind == ARRAYSYM ?  tokb->intval = recV->datatype->size * (recV->datatype->highbound - recV->datatype->lowbound + 1) : 0;
 		tokb = makeintc(intTok);
    int tokValues = val->datatype->kind != ARRAYSYM ? -recV->size : 
      val->kind == ARRAYSYM && searchst(subs->link->stringval)->kind == CONSTSYM ? 
        -(searchst(subs->link->stringval)->constval.intnum + 1)*recV->datatype->size : tok -> intval;
    tok -> intval = tokValues;
    if (val->datatype->kind == ARRAYSYM && val->kind == ARRAYSYM){
      subs-> link = NULL;
    } else {
      subs-> link;
    }
    tokb->link = subs;
 		TOKEN multiply = makeop(TIMESOP);
    unaryop(multiply, tokb);
    cons(tok, multiply);
 		ret->symtype = val;
 		return ret;
 	}
 	return tok;
}

//c
/* makeintc makes a new token with num as its value */
TOKEN makeintc(int num) {
  TOKEN tok = talloc();
  tok->tokentype = NUMBERTOK;
  tok->basicdt = INTEGER;
  tok->intval = num;
  return tok;
}


//c
/* makearef makes an array reference operation.
   off is be an integer constant token
   tok (if not NULL) is a (now) unused token that is recycled. */
TOKEN makearef(TOKEN var, TOKEN off, TOKEN tok){
  var->link = off;
  TOKEN result = tok;
  if (tok == NULL)
 	  result = makeop(AREFOP);
  unaryop(result, var);
  result->tokentype = OPERATOR;
 	result->whichval = AREFOP;
 	return result;
}

//c
TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {
	SYMBOL r =  var->symtype;
  int base = 0;
  int val = 0;
  SYMBOL rCheck;
 	if (var->whichval == AREFOP) { 
   	r = r->datatype->datatype->datatype;
 	} else {
    SYMBOL ptr = searchst(var->link->stringval);
    if (var->link->whichval != AREFOP){
      rCheck = ptr-> datatype;
    } else {
      rCheck = var->link->symtype->datatype;
    }
    r =  rCheck -> datatype->datatype->datatype->datatype;
    unaryop(var, var->link);
 	}
  while (r && strcmp(field->stringval, r->namestring)) {
    if (r->datatype->size == basicsizes[INTEGER && r->link->datatype->size == basicsizes[REAL]]) {
      r->datatype->size = basicsizes[REAL];
    } else {
 	  	val += r->datatype->size;
      r = r -> link;
    }
  }
  base =searchst(r->datatype->namestring) &&  !strcmp(field->stringval, r->namestring) ? searchst(r->datatype->namestring)->basicdt :  base;
  TOKEN array = makeop(AREFOP);
 	if (var->whichval != AREFOP) {
    TOKEN tok = makeintc(val);
 		array = makearef(var, tok, dot);
 		array->basicdt = base;
 		array->whichval = AREFOP;
 		array->symtype = r;
 	} else {
 		if (var->operands->link->tokentype == NUMBERTOK) {
 			var->operands->link->intval += val;
    }
    array = var;
    array->basicdt = base;
 	}
 	return array;
}

//c
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

//c
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
    rhs = makefix(rhs);
  } else if (!op->whichval == ASSIGNOP &&  leftInt && rightR) {
    lhs  = makefloat(lhs);
  }
  cons(rhs, NULL);
  cons(lhs, rhs);
  unaryop(op, lhs);
  return op;
}

//c
TOKEN unaryop(TOKEN op, TOKEN lhs) {
	op->operands = lhs;
	return op;
}

//c
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

//c
TOKEN makeprogn(TOKEN tok, TOKEN statements) {  
	tok->tokentype = OPERATOR;
    tok->whichval = PROGNOP;
    tok->operands = statements;
    return tok;
}

//c
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

//c
TOKEN makegoto(int label) {
  TOKEN r = talloc();
  r -> whichval = GOTOOP;
  r -> operands = makeintc(label);
  r -> tokentype = OPERATOR;
  return r;
}

//c
TOKEN makelabel() {
  TOKEN r = makeop(LABELOP);
  r -> operands = makeintc(labelnumber);
  labelnumber++;
  return r;
}

//c
TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement) {
 	TOKEN label = makelabel();
  label->link = makeif(tok, expr, statement, NULL);
  int lab = labelnumber -1;
  TOKEN check = statement->operands;
 	while(check->link){
    check = check->link;
   }
 	check->link = makegoto(lab);
 	return makeprogn(tokb, label);
}

//c
TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr, TOKEN tokc, TOKEN statement) {
  TOKEN zero = makelabel();
  TOKEN getTok =makeop(ASSIGNOP);
  TOKEN start = talloc();
  start->tokentype = IDENTIFIERTOK;
  strcpy(start->stringval, asg->operands->stringval);
  zero->link = makeif(tok, binop(makeop(LEOP), start, endexpr), makeprogn(tokc, statement), NULL);
  asg->link = zero;
  statement->link = getTok;
  asg->link = zero;
  cons(getTok, makegoto(zero->operands->intval));
  TOKEN identificationInit = talloc();
  unaryop(getTok, identificationInit);
  getTok->operands = identificationInit;
  identificationInit->tokentype = IDENTIFIERTOK;
  identificationInit->link = makeplus(talloc(), makeintc(1), talloc());
  strcpy(identificationInit->stringval, asg->operands->stringval);
  identificationInit->link->operands->tokentype = IDENTIFIERTOK;
  strcpy(identificationInit->link->operands->stringval, asg->operands->stringval);
  return makeprogn(tokb, asg);
}

//c
TOKEN makeplus(TOKEN lhs, TOKEN rhs, TOKEN tok) {
    TOKEN increment = makeop(PLUSOP);
    increment -> operands = lhs;
    lhs -> link = rhs;
    return increment;
}

//c
TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr) {
  cons(makelabel(), statements);
  while(statements -> link) {
    statements = statements -> link;
  }
	statements->link = makeif(tokb, expr, makeprogn(talloc(), NULL), makegoto(labelnumber - 1));
	return makeprogn(tok, makelabel());
}


//c 
/* install variables in symbol table */
void instvars(TOKEN idlist, TOKEN typetok) {
  while(idlist) {
    SYMBOL symbolCheck = insertsym(idlist->stringval);
		symbolCheck->kind = VARSYM;
    int typesSym = typetok->symtype == NULL;
    if (typesSym){
      symbolCheck->datatype = searchins(typetok->stringval);
    } else {
      symbolCheck->datatype = typetok->symtype;
    }
    symbolCheck->basicdt = symbolCheck->datatype->basicdt;
		symbolCheck->size = symbolCheck->datatype->size;
    if (symbolCheck->size >= 16){
      blockoffs[symbolCheck->blocklevel] += blockoffs[symbolCheck->blocklevel] % 16;
    }
		symbolCheck->blocklevel = 1;
		symbolCheck->offset = blockoffs[1];
		blockoffs[1] += symbolCheck->size;
    idlist = idlist->link;
  }
}

//c
/* makesubrange makes a SUBRANGE symbol table entry, puts the pointer to it
   into tok, and returns tok. */
TOKEN makesubrange(TOKEN tok, int low, int high) {
  SYMBOL subrange = symalloc();
  subrange->kind = SUBRANGE;
  subrange->basicdt = INTEGER;
  subrange->lowbound = low;
  subrange->highbound = high;
  subrange->size = basicsizes[INTEGER];
  tok->symtype = subrange;
  return tok;
}


//c
TOKEN instenum(TOKEN idlist) {
  int val = 0;
  while(idlist) {
    instconst(idlist, makeintc(val));
    val++;
    idlist = idlist -> link;
  }
  TOKEN input = talloc();
  return makesubrange(input, 0, val - 1); 
}

//c
TOKEN instdotdot(TOKEN lowtok, TOKEN dottok, TOKEN hightok) {
  return makesubrange(dottok, lowtok->intval, hightok->intval);
}

//c
/* insttype will install a type name in symbol table.
   typetok is a token containing symbol table pointers. */
void  insttype(TOKEN typename, TOKEN typetok) {
  SYMBOL typesym = searchins(typename->stringval);
  typesym->kind = TYPESYM;
  typesym->size = typetok->symtype->size;
  typesym->datatype = typetok->symtype;
}

//c
TOKEN instfields(TOKEN idlist, TOKEN typetok) {
  TOKEN r = idlist;
  while(idlist) {
    idlist -> symtype = searchins(typetok->stringval);;
    idlist = idlist-> link;
  }
 	return r;
}

//c
TOKEN instpoint(TOKEN tok, TOKEN typename) {
  SYMBOL pointer = symalloc();
  pointer->kind = POINTERSYM;
  pointer->datatype = searchins(typename->stringval);
  pointer -> size = basicsizes[POINTER];
  pointer -> basicdt = POINTER;
  tok->symtype = pointer;
 	return tok;
}

//c
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
    if (argstok->symtype != NULL){
      size += argstok->symtype->size;
      val->datatype = argstok->symtype;
    }
 	}
 	record->size = wordaddress(size, 16);
 	rectok->symtype = record;
 	return rectok;
}


//c
/* instlabel installs a user label into the label table */
void  instlabel (TOKEN num) {
  labels[labelnumber++] = num->intval;
}

//c
/* instconst installs a constant in the symbol table */
void  instconst(TOKEN idtok, TOKEN consttok) {
  SYMBOL sym = insertsym(idtok->stringval);
  sym->kind = CONSTSYM;
  sym->basicdt = consttok->basicdt;
  if(sym->basicdt == REAL) {
    sym->constval.realnum = consttok->realval;
  } else if (sym->basicdt == INTEGER) {
    sym->constval.intnum = consttok->intval;
  }
}

//c 
/* instarray installs an array declaration into the symbol table.
   bounds points to a SUBRANGE symbol table entry.
   The symbol table pointer is returned in token typetok. */
TOKEN instarray(TOKEN bounds, TOKEN typetok) {
 	TOKEN result = talloc();
  SYMBOL sym = symalloc();
	sym->kind = ARRAYSYM;
	sym->lowbound = bounds -> symtype->lowbound;
	sym->highbound = bounds -> symtype->highbound;
  int add = (sym->highbound - sym->lowbound + 1);
  if (bounds->link == NULL){
    sym->datatype = searchst(typetok->stringval);
  } else {
    sym->datatype = symalloc();
  }
	sym->size += add * searchst(typetok->stringval)->size;
	if (bounds->link) {
		bounds = bounds->link;
		SYMBOL rangeSym = searchst(bounds->stringval) -> datatype;
		sym->datatype = symalloc();
		sym->datatype->lowbound = rangeSym->lowbound;
		sym->datatype->highbound = rangeSym->highbound;
    int mult = (sym->datatype->highbound - sym->datatype->lowbound + 1);
		sym->size *= mult;
		sym->datatype->kind = ARRAYSYM;
		sym->datatype->datatype = searchst(typetok->stringval);
	}
	result->symtype = sym;
	return result;
}

//c
/* makeprogram makes the tree structures for the top-level program */
TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements) {
    TOKEN nameProg = talloc();
    TOKEN statementProg = talloc();
    TOKEN result = talloc();
    result->tokentype = OPERATOR;
    result->whichval = PROGRAMOP;
    makeprogn(nameProg, args);
    unaryop(result, name);
    makeprogn(statementProg, statements);
    cons(nameProg, statementProg);
    cons(name, nameProg);
    return result;
  }

//c
int wordaddress(int n, int wordsz) {
	return ((n + wordsz - 1) / wordsz) * wordsz; }
 
void yyerror (char const *s) {
  	fprintf (stderr, "%s\n",s);
}

int main(void) { 
	int res;
    	initsyms();
    	res = yyparse();
    	printst();       /* to shorten, change to:  printstlevel(1);  */
    	printf("yyparse result = %8d\n", res);
    	if (DEBUG) dbugprinttok(parseresult);
    	ppexpr(parseresult);           /* Pretty-print the result tree */
    	/* uncomment following to call code generator. */
	  	//gencode(parseresult, blockoffs[blocknumber], labelnumber);
  }
