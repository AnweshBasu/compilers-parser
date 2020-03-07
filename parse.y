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

program    :  PROGRAM IDENTIFIER LPAREN id_list RPAREN SEMICOLON vblock DOT   { parseresult = makeprogram($2, $4, $7); }
             ;
  statement  :  BEGINBEGIN statement endpart
                                       { $$ = makeprogn($1,cons($2, $3)); }
             |  IF expression THEN statement endif   { $$ = makeif($1, $2, $4, $5); }
             | FOR assignment TO expression DO statement {$$  = makefor(1, $1, $2, $3, $4, $5, $6);}
             | funcall {$$ = $1;}
             |  assignment 
             ;
  funcall    :  IDENTIFIER LPAREN expression_list RPAREN {$$ = makefuncall($2, $1, $3);}
             ;
  expression_list  : expression COMMA expression_list  {$$ = cons($1, $3);}
             | expression  {$$ = cons($1, NULL);}     
             ;
  endpart    :  SEMICOLON statement endpart    { $$ = cons($2, $3); }
             |  END                            { $$ = NULL; }
             ;
  endif      :  ELSE statement                 { $$ = $2; }
             |  /* empty */                    { $$ = NULL; }
             ;
  assignment :  variable ASSIGN expression           { $$ = binop($2, $1, $3); }
             ;
  expression :  expression PLUS term                 { $$ = binop($2, $1, $3); }
             |  term 
             ;        
  term       :  term TIMES factor              { $$ = binop($2, $1, $3); }
             |  factor
             ;
  factor     :  LPAREN expression RPAREN             { $$ = $2; }
             |  IDENTIFIER      
             |  variable
             |  NUMBER
             ;
  variable   : IDENTIFIER
             ;
  id_list    : IDENTIFIER COMMA id_list  {$$ = cons($1, $3);}
             | IDENTIFIER  {$$ = cons($1, NULL);}
             ;
  vblock     : VAR v_list block  {$$ = $3;}
             | block
             ;
  v_list     : v_grp_def SEMICOLON  v_list  {$$ = cons($2, $1);}
             |  v_grp_def SEMICOLON    {$$ = $1;}
             ;
  v_grp_def       : id_list COLON type {instvars($1, $3);}
             ;           
  type       : simp_type  {$$ = $1;}            
             ;
  simp_type  : IDENTIFIER
             ;
  block      :  BEGINBEGIN statement endpart  {$$ =  makeprogn($1,cons($2, $3));}
             ;             
%%

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.
  */

#define DEBUG        31             /* set bits here for debugging, 0 = off  */
#define DB_CONS       1             /* bit to trace cons */
#define DB_BINOP      2             /* bit to trace binop */
#define DB_MAKEIF     4             /* bit to trace makeif */
#define DB_MAKEPROGN  8             /* bit to trace makeprogn */
#define DB_PARSERES  16             /* bit to trace parseresult */

 int labelnumber = 0;  /* sequential counter for internal label numbers */

   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */

TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
  { item->link = list;
    if (DEBUG & DB_CONS)
       { printf("cons\n");
         dbugprinttok(item);
         dbugprinttok(list);
       };
    return item;
  }

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs)        /* reduce binary operator */
  { op->operands = lhs;          /* link operands to operator       */
    lhs->link = rhs;             /* link second operand to first    */
    rhs->link = NULL;            /* terminate operand list          */
    if (DEBUG & DB_BINOP)
       { printf("binop\n");
         dbugprinttok(op);
         dbugprinttok(lhs);
         dbugprinttok(rhs);
       };
    return op;
  }

/* makeop makes a new operator token with operator number opnum.
   Example:  makeop(FLOATOP)  */
TOKEN makeop(int opnum) {
  TOKEN operatorTok = talloc();
  operatorTok -> tokentype = OPERATOR;
  operatorTok -> whichval = opnum;
  return operatorTok;  
}

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart)
  {  tok->tokentype = OPERATOR;  /* Make it look like an operator   */
     tok->whichval = IFOP;
     if (elsepart != NULL) elsepart->link = NULL;
     thenpart->link = elsepart;
     exp->link = thenpart;
     tok->operands = exp;
     if (DEBUG & DB_MAKEIF)
        { printf("makeif\n");
          dbugprinttok(tok);
          dbugprinttok(exp);
          dbugprinttok(thenpart);
          dbugprinttok(elsepart);
        };
     return tok;
   }

/* makeintc makes a new integer number token with num as its value */
TOKEN makeintc(int num) { 
  TOKEN intcTok = talloc();
  intcTok-> tokentype = NUMBERTOK;
  intcTok -> intval = num;
  intcTok -> basicdt = INTEGER;
  return intcTok;
}

/* makelabel makes a new label, using labelnumber++ */
TOKEN makelabel() {
  TOKEN labelTok = makeop(LABELOP);
  labelTok -> operands = makeintc(labelnumber);
  labelnumber++;
  return labelTok;
}

/* makegoto makes a GOTO operator to go to the specified label.
   The label number is put into a number token. */
TOKEN makegoto(int label) {
  TOKEN gotoTok = talloc();
  gotoTok -> whichval = GOTOOP;
  TOKEN intcTok = makeintc(label);
  gotoTok -> operands = intcTok;
  gotoTok -> tokentype = OPERATOR;
  return gotoTok;
}

/* makefuncall makes a FUNCALL operator and links it to the fn and args.
   tok is a (now) unused token that is recycled. */
TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) 
{
  TOKEN funcallTok = makeop(FUNCALLOP);
  funcallTok -> operands = fn;
  fn -> link = args;
  return funcallTok; /*makeprogn(tok, funcallTok);*/
}

/* makefor makes structures for a for statement.
   sign is 1 for normal loop, -1 for downto.
   asg is an assignment statement, e.g. (:= i 1)
   endexpr is the end expression
   tok, tokb and tokc are (now) unused tokens that are recycled. */
TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr,
              TOKEN tokc, TOKEN statement) 
{
    TOKEN labelZero = makelabel();
                asg -> link = labelZero;
                TOKEN lessThan  = makeop(LEOP);
                TOKEN identifier = talloc();
                identifier -> tokentype = IDENTIFIERTOK;
                strcpy(identifier -> stringval, asg ->operands -> stringval);
                TOKEN ifStatement = binop(lessThan, identifier, endexpr);
                labelZero -> link = makeif(tok, ifStatement, statement, NULL);
                TOKEN variableIncrement = talloc();
                variableIncrement -> tokentype = IDENTIFIERTOK;
                strcpy(variableIncrement -> stringval, identifier -> stringval);

                TOKEN increment =  makeplus(variableIncrement, makeintc(1), talloc());
                TOKEN variableAssign = talloc();
                variableAssign -> tokentype = IDENTIFIERTOK;
                strcpy(variableAssign -> stringval, identifier -> stringval);
                increment -> operands =  variableIncrement;
                 variableAssign -> link = increment;
                TOKEN sepAsign = makeop(ASSIGNOP);
                sepAsign -> operands = variableAssign;
                TOKEN stateOps = statement -> operands;
                stateOps -> link = sepAsign;
                sepAsign -> link = makegoto(labelZero -> operands -> intval);
		    return makeprogn(tokb, asg);
}



TOKEN makeprogn(TOKEN tok, TOKEN statements)
{  tok->tokentype = OPERATOR;
   tok->whichval = PROGNOP;
   tok->operands = statements;
   if (DEBUG & DB_MAKEPROGN)
     { printf("makeprogn\n");
       dbugprinttok(tok);
       dbugprinttok(statements);
     };
   return tok;
 }

/* makeprogram makes the tree structures for the top-level program */
TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements)
{
  TOKEN progNameTok = talloc();
  TOKEN progTok  = makeop(PROGRAMOP);
  progTok -> operands = name;
  progNameTok = makeprogn(progNameTok, args);
  name -> link = progNameTok;
  progNameTok -> link = statements;
  return progTok;  
}

int wordaddress(int n, int wordsize)
  { return ((n + wordsize - 1) / wordsize) * wordsize; }
 
/* instvars will install variables in symbol table.
   typetok is a token containing symbol table pointer for type. */
void  instvars(TOKEN idlist, TOKEN typetok)
{
  int token_alignment = alignsize(searchst(typetok -> stringval));
  for (;idlist != NULL; idlist = idlist -> link) {
      SYMBOL symVal = insertsym(idlist -> stringval);
      symVal -> basicdt = idlist -> basicdt;
      symVal -> kind = VARSYM;
      symVal -> size = searchst(typetok -> stringval) -> size;
      symVal -> datatype = searchst(typetok -> stringval);
      symVal -> offset = wordaddress(blockoffs[blocknumber], token_alignment);
      int replace = symVal -> size + symVal -> offset;     
      blockoffs[blocknumber] = replace;
  }
}


void yyerror (char const *s)
{
  fprintf (stderr, "%s\n", s);
}

int main(void)          /*  */
  { int res;
    initsyms();
    res = yyparse();
    printst();       /* to shorten, change to:  printstlevel(1);  */
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
    /* uncomment following to call code generator. */
     /* 
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
 */
  }
