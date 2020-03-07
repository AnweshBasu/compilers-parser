%{    /* lex2.l -- partial lex specification for Pascal   20 Feb 19 */

/* Copyright (c) 2019 Gordon S. Novak Jr. and The University of Texas at Austin
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
int install_id();
int install_fnum();
int yywrap();
int install_number();
int install_string();

/* If the lex yytext buffer turns out to be too small to hold comments,
   add the following lines:
 #undef YYLMAX
 #define YYLMAX 256
 */

TOKEN yylval;     /* This is the type of the lexical analyzer result */

%}

/* regular definitions */

delim    [ \t\n]
comments \{[^\}]+\}
ws       {delim}+
letter   [A-Za-z]
digit    [0-9]
id       {letter}({letter}|{digit})*
fnumber  {digit}+(\.{digit}+)?([eE][+\-]?{digit}+)?
number   {digit}+
string   (\'(.)*?\')

%%

{ws}      { /* no action and no return */ }
{comments} { /* no action and no return */ }  

"(*"       {     loop:
                  while (input() != '*');
                  switch (input())
                  {
                    case ')': break;
                    case '*': unput('*');
                    default: goto loop;
                  }
          }


"+"       {return(maketoken(OPERATOR, PLUS));}
"-"       {return(maketoken(OPERATOR, MINUS));}
"*"       {return(maketoken(OPERATOR, TIMES));} 
"/"       {return(maketoken(OPERATOR, DIVIDE));}
":="      {return(maketoken(OPERATOR, ASSIGN));}
"="       {return(maketoken(OPERATOR, EQ));}
"<>"      {return(maketoken(OPERATOR, NE));}
"<"       {return(maketoken(OPERATOR, LT));}
"<="      {return(maketoken(OPERATOR, LE));}
">="      {return(maketoken(OPERATOR, GE));}
">"       {return(maketoken(OPERATOR, GT));}
"^"       {return(maketoken(OPERATOR, POINT));} 
"."       {return(maketoken(OPERATOR, DOT));}

","       {return(maketoken(DELIMITER, COMMA));}
";"       {return(maketoken(DELIMITER, SEMICOLON));}
":"       {return(maketoken(DELIMITER, COLON));}
"("       {return(maketoken(DELIMITER, LPAREN));}
")"       {return(maketoken(DELIMITER, RPAREN));}
"["       {return(maketoken(DELIMITER, LBRACKET));}
"]"       {return(maketoken(DELIMITER, RBRACKET));}
".."      {return(maketoken(DELIMITER, DOTDOT));}  


array        {return(maketoken(RESERVED, ARRAY));}
downto       {return(maketoken(RESERVED, DOWNTO));}
function     {return(maketoken(RESERVED, FUNCTION));}
of           {return(maketoken(RESERVED, OF));}
repeat       {return(maketoken(RESERVED, REPEAT));}
until        {return(maketoken(RESERVED, UNTIL));}
begin        {return(maketoken(RESERVED, BEGINBEGIN));}
else         {return(maketoken(RESERVED, ELSE));}
goto         {return(maketoken(RESERVED, GOTO));}
packed       {return(maketoken(RESERVED, PACKED));}
set          {return(maketoken(RESERVED, SET));}
var          {return(maketoken(RESERVED, VAR));}
case         {return(maketoken(RESERVED, CASE));}
end          {return(maketoken(RESERVED, END));}
if           {return(maketoken(RESERVED, IF));}
procedure    {return(maketoken(RESERVED, PROCEDURE));}
then         {return(maketoken(RESERVED, THEN));}
while        {return(maketoken(RESERVED, WHILE));}
const        {return(maketoken(RESERVED, CONST));}
file         {return(maketoken(RESERVED, FILEFILE));}
label        {return(maketoken(RESERVED, LABEL));}
program      {return(maketoken(RESERVED, PROGRAM));}
to           {return(maketoken(RESERVED, TO));}
with         {return(maketoken(RESERVED, WITH));}
do           {return(maketoken(RESERVED, DO));}
for          {return(maketoken(RESERVED, FOR));}
nil          {return(maketoken(RESERVED, NIL));}
record       {return(maketoken(RESERVED, RECORD));}
type         {return(maketoken(RESERVED, TYPE));}

{id}      {return(install_id());}
{number}  {return(install_number());}
{fnumber} {return(install_fnum());}
{string}  {return(install_string());}


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

int install_number() {
  int number;
  yylval = (TOKEN) talloc();
  yylval->tokentype = NUMBERTOK;
  yylval->basicdt = INTEGER;
  /* printf("num %10s   n = %4d\n",yytext,yyleng); */
  sscanf(yytext, "%d", &number);
  yylval->intval = number;
  return(NUMBER);
}


int install_string(){
  int size = 0, i = 1, numQt = 0,length = yyleng;
  yylval = (TOKEN) talloc();
  yylval -> tokentype = STRINGTOK;
  for(;i < length;i++){
     if(yytext[i]=='\''&& yytext[i+1]=='\''){
      yylval->stringval[size] = yytext[i];
      i ++;
      numQt++;
    }else{
      yylval->stringval[size] = yytext[i];  
    }
      size++;;
  }
  if(size > 15){
    yylval->stringval[15-numQt] = '\0';
  } else {
    yylval->stringval[size-1] = '\0'; /* adjust for ' */
  }
  return(STRING);
}

int yywrap() {  return(1);  }       /* lex may need this. */
