%{    /* lex2.l -- partial lex specification for Pascal   11 Jan 18 */

/* Copyright (c) 2013 Gordon S. Novak Jr. and The University of Texas at Austin
   */
/* 22 Jul 13
   */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, see <http://www.gnu.org/licenses/>. */

/* To use:
        make lex2
        lex2
        x < 3.14            */

/* This file will work as given on a simple input such as:
   if i<j then x := 3.14

   Copy this file to lexan.l and expand it for your assignment.
   Use:
        make lexer
        lexer <graph1.pas
   */

#include <ctype.h>
#include "token.h"
#include "lexan.h"

int maketoken(int type, int which);
int install_num();
int install_id();
int install_fnum();
int install_string();
int yywrap();

/* If the lex yytext buffer turns out to be too small to hold comments,
   add the following lines:
 #undef YYLMAX
 #define YYLMAX 256
 */

TOKEN yylval;     /* This is the type of the lexical analyzer result */

%}

/* regular definitions */

symbols [-.]
string (\'(.)*\')
delim    [ \t\n]
ws       {delim}+
bracket  (\{[^\{\}]+\})
letter   [A-Za-z]
digit    [0-9]
number  ({digit}+)
id       {letter}({letter}|{digit})*
single_quote  (\'{1})
fnumber  {digit}+(\.{digit}+)?(E[+\-]?{digit}+)?
enumber  {digit}+(\.{digit}+)?(e[+\-]?{digit}+)?
%%



{ws}      { /* no action and no return */ }
{bracket} { /* no action and no return */ }
""      { /* no action and no return */ }
"(*"    {       loop:
                while (input() != '*');
                switch (input())
                        {
                        case ')': break;
                        case '*': unput('*');
                        default: goto loop;
                        }
                }
if        {return(maketoken(RESERVED, IF));}
then      {return(maketoken(RESERVED, THEN));}
else      {return(maketoken(RESERVED, ELSE));}
begin     {return(maketoken(RESERVED, BEGINBEGIN));}
end       {return(maketoken(RESERVED, END));}
program   {return(maketoken(RESERVED, PROGRAM));}
const     {return(maketoken(RESERVED, CONST));}
var       {return(maketoken(RESERVED, VAR));}
do       {return(maketoken(RESERVED, DO));}
for       {return(maketoken(RESERVED, FOR));}
repeat    {return(maketoken(RESERVED, REPEAT));}
until     {return(maketoken(RESERVED, UNTIL));}
to     {return(maketoken(RESERVED, TO));}
"-"       {return(maketoken(OPERATOR, MINUS));}
"+"       {return(maketoken(OPERATOR, PLUS));}
"<"       {return(maketoken(OPERATOR, LT));}
"<="      {return(maketoken(OPERATOR, LE));}
"="       {return(maketoken(OPERATOR, EQ));}
"<>"      {return(maketoken(OPERATOR, NE));}
">"       {return(maketoken(OPERATOR, GT));}
">="      {return(maketoken(OPERATOR, GE));}
":="      {return(maketoken(OPERATOR, ASSIGN));}
".."       {return(maketoken(DELIMITER, DOTDOT));}
"."       {return(maketoken(OPERATOR, DOT));}
";"       {return(maketoken(DELIMITER, SEMICOLON));}
"("       {return(maketoken(DELIMITER, LPAREN));}
")"       {return(maketoken(DELIMITER, RPAREN));}
","       {return(maketoken(DELIMITER, COMMA));}
":"       {return(maketoken(DELIMITER, COLON));}
"*"       {return(maketoken(OPERATOR, TIMES));}
{id}      {return(install_id());}
{string} {return(install_string());}
{number} {return(install_num());}
{fnumber} {return(install_fnum());}
{enumber} {return(install_fnum());}

%%

/* Note that lex always returns two values:
   1. "What is it?": a small integer such as NUMBER that indicates the
      kind of item that was found; this is the return() value.
   2. The value itself.  This is yylval, which points to a TOKEN.   */

/* Make simple tokens. */
int maketoken(int type, int which)
  {
  yylval = (TOKEN) talloc();  /* Make new token, set yylval to point to it */
  yylval->tokentype = type;
  if (type == RESERVED)
     yylval->whichval = which - RESERVED_BIAS;
     else if (type == OPERATOR)
             yylval->whichval = which - OPERATOR_BIAS;
             else if (type == DELIMITER)
                     yylval->whichval = which - DELIMITER_BIAS;
                     else yylval->whichval = which;
  return(which);
  }

int install_id()
 { int i, c, n;
  yylval = (TOKEN) talloc();  /* Make new token, set yylval to point to it */
  yylval->tokentype = IDENTIFIERTOK;
  n = yyleng;            /* number of characters */
  if ( n > 15 ) n = 15;
  for (i = 0; i < n ; i++)
   { c = yytext[i];
          /* if (islower(c)) c = toupper(c); */ /* to raise to upper case */
     yylval->stringval[i] = c;
    };
  yylval->stringval[n] = '\0';
          /* printf("id  %10s   n = %4d\n", yytext, n); */
  return(IDENTIFIER);
 }

int install_fnum() {  /* Note -- you may use sscanf for this assignment. */
  float fnum;
  yylval = (TOKEN) talloc();   /* Make new token, set yylval to point to it */
  yylval->tokentype = NUMBERTOK;
  yylval->basicdt = REAL;
       /* printf("num %10s   n = %4d\n",yytext,yyleng); */
  sscanf(yytext, "%f", &fnum);
  yylval->realval = fnum;
  return(NUMBER);
 }

 int install_num() {  /* Note -- you may use sscanf for this assignment. */
  int num;
  yylval = (TOKEN) talloc();   /* Make new token, set yylval to point to it */
  yylval->tokentype = NUMBERTOK;
  yylval->basicdt = INTEGER;
       /* printf("num %10s   n = %4d\n",yytext,yyleng); */
  sscanf(yytext, "%d", &num);
  yylval->intval = num;
  return(NUMBER);
 }
 
 int install_string()
 { int i, c, n;
  yylval = (TOKEN) talloc();  /* Make new token, set yylval to point to it */
  yylval->tokentype = STRINGTOK;
  n = yyleng;            /* number of characters */
  if ( n > 17 ) n = 17;
  int decrement = 0;
  for (i = 1; i < n - 1; i++)
   { 
     c = yytext[i];
          /* if (islower(c)) c = toupper(c); */ /* to raise to upper case */
        if (c == '\'' && yytext[i - 1] == '\'') {
                decrement++;
        }
        yylval->stringval[i - 1 - decrement] = c;
    };
  yylval->stringval[n] = '\0';
          /* printf("id  %10s   n = %4d\n", yytext, n); */
  return(STRING);
 }

int yywrap() {  return(1);  }       /* lex may need this. */
