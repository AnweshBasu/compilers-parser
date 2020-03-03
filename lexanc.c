/* lex1.c         14 Feb 01; 31 May 12; 11 Jan 18       */

/* This file contains code stubs for the lexical analyzer.
   Rename this file to be lexanc.c and fill in the stubs.    */

/* Copyright (c) 2018 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/*
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <limits.h>
#include <math.h>
#include <float.h>
#include "token.h"
#include "lexan.h"

/* This file will work as given with an input file consisting only
   of integers separated by blanks:
   make lex1
   lex1
   12345 123    345  357
 */

const char* operators[] = { "+", "-", "*", "/", ":=", "=", "<>", "<", "<=", 
                            ">=", ">", "^", ".", "and", "or", "not", "div", 
                            "mod", "in" };

const char* delimiters[] = { ",", ";", ":", "(", ")", "[", "]", ".."};

const char* reservedWords[] = { "array", "begin", "case", "const", "do", 
                                "downto", "else", "end", "file", "for", 
                                "function", "goto", "if", "label", "nil", 
                                "of", "packed", "procedure", "program", 
                                "record", "repeat", "set", "then", "to", 
                                "type", "until", "var", "while", "with"};

/* Skip blanks and whitespace.  Expand this function to skip comments too. */
void skipblanks ()
{
  int c, d;
  while ((c = peekchar()) != EOF ){
    if (c == ' ' || c == '\n' || c == '\t') {
      getchar();
    } else if (c == '{'){
      while ((c = peekchar()) != EOF && (c != '}'))
      {
        getchar();
      }
      getchar();
    } 
    else if (c == '(' && (d = peek2char()) != EOF && d == '*')
    {
      getchar();
      getchar();  
      while ((c = peekchar()) !=  EOF && (d = peek2char()) != EOF 
            && !(c == '*' && d== ')'))
      {
        getchar();
      }
      getchar();
      getchar(); 
    } 
    else 
    {
      break;
    }
  }
}


/* Get identifiers and reserved words */
TOKEN identifier (TOKEN tok)
{
  int  c, count, size = 0;    
  char variable[16];
  //read in up to 15 characters for identifier
  while ( (c = peekchar()) != EOF &&(CHARCLASS[c] == ALPHA 
        || CHARCLASS[c] == NUMERIC) && size < 15) 
  {
    variable[size] = getchar();
    size += 1;
  }
  //consume extra characters
  if (size >= 15)
  {
    while ((c = peekchar()) != EOF && (CHARCLASS[c] == ALPHA || CHARCLASS[c] == NUMERIC))
      {
        getchar();
      }
  }
  variable[size] = '\0';

  // check for word operator
  for (count = 13; count <= 18 ; count++)
  {
    if (strcmp(variable, operators[count]) == 0)
    {
      tok->tokentype = OPERATOR;
      tok->whichval = count+1;
      return tok;
    }
  }

  //check for reserved word
  for (count = 0;  count <= 28; count++)
  {
    if (strcmp(variable, reservedWords[count]) == 0)
    {
      tok->tokentype = RESERVED;
      tok->whichval = count+1;
      return tok;
    }
  }
  //it is an identifier
  tok->tokentype = IDENTIFIERTOK;
  strcpy(tok->stringval, variable);
  return tok;
}

TOKEN getstring (TOKEN tok)
{
  getchar(); //starting '
  char string[16];
  int c, d, size = 0;

  //read in up to 15 characters for a string  
  while (!((c = peekchar()) != EOF && c== '\'' && (d = peek2char()) != EOF 
        && d !='\'') && size < 15)
  {
    if (!(c != '\'' || d != '\'')) //escaped '
    {
      getchar();
    }
    c = getchar();

    if (c == ' ') 
    {
      string[size] = ' ';
      size+=1;
    } 
    else 
    {
      string[size] = c;
      size+=1;
    }
    
  }
  //consume the extra characters
  if (size >= 15) 
  {
    while (!((c = peekchar()) != EOF && c == '\'' 
      && (d = peek2char()) != EOF && d!= '\''))
    {
      getchar();
    }
  }
  string[size] = '\0';
  getchar(); //ending '

  tok->tokentype = STRINGTOK;
  strcpy(tok->stringval, string);
  return tok;

}


TOKEN special (TOKEN tok)
{    
  int count, size = 0;
  char c, d;    
  char special[3];
  //read 1 or two charactes for special
  while ( (c = peekchar()) != EOF
        && (size <= 3) && (CHARCLASS[c] == SPECIAL)) 
  {
    special[size] = getchar();
    size += 1;  
    d = peekchar();    
    if(d != EOF) 
    {
      //check for operator/delimiter that has 2 characters
      if ((c == ':' && d == '=') || (c == '<' && (d == '>' || d == '=')) 
         || (c == '>' && d == '=') || (c == '.' && d == '.')) 
      {
        special[size] = getchar();
        size += 1;
      } else {
        break;
      }
    }
  }
  special[size] = '\0';

  //check non word operators
  for (count = 0; count <= 12 ; count++)
  {
    if (strcmp(special, operators[count]) == 0)
    {
      tok->tokentype = OPERATOR;
      tok->whichval = count+1;
      return tok;
    }
  }
  //check delimiters
  for (count = 0; count <= 7 ; count++)
  {
    if (strcmp(special, delimiters[count]) == 0)
    {
      tok->tokentype = DELIMITER;
      tok->whichval = count+1;
      return tok;
    }
  }
}


/* Get and convert unsigned numbers of all types. */
TOKEN number (TOKEN tok)
{   
  int  c = 0, d = 0, intVal = 0, isFloat = 0, isExponent = 0, 
       negativeNo = 0, intError = 0;
  long num = 0, exponent = 0, exponentPart = 0;
  double divideAdjustment = 1.0, decimalPart = 0.0, floatNo = 0.0;
  //get the integer part of the number
  while ( (c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC)
  {   
    intVal = (getchar() - '0');
      if ( num > INT_MAX ) 
    {     
      //number is too big as int so move to exponent
        exponent --;
        intError = 1;
      } 
    else 
    {     
      num = num * 10 + intVal;
    }
  }
  //last digit makes it too big
  if ( num > INT_MAX ) 
  {
    intError = 1;
  } 

  //look at the part after the decimal point
  if ((c = peekchar()) != EOF &&  c == '.') {
    if ((d = peek2char()) != EOF && CHARCLASS[d] == NUMERIC) 
    {
      c = getchar();
      intError = 0; //floating point number has higher max
      isFloat = 1;
      //store the decimal part of the number
      while ((c = peekchar()) != EOF && (CHARCLASS[c] == NUMERIC)) 
      {
        intVal = getchar() - '0';
        divideAdjustment *= 10;
        decimalPart = decimalPart + ((double)intVal/divideAdjustment); 
      }
      floatNo = (double) num + decimalPart; 
    }
  } 
  else //if there is no decimal part store existing int as float
  {
    floatNo = (double)num;
  }
  
  //look at the exponent part of the number
  if ((c = peekchar()) != EOF &&  c == 'e')
  {
    c = getchar();
    isExponent = 1;
    int sign = 1;
    //store the sign
    sign *= (c = peekchar()) == '-' ? 1 : -1;
    if ((c = peekchar()) != EOF && CHARCLASS[c] != NUMERIC)
    {
      getchar(); //consume sign
    }
    //store the exponent part
    while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) 
    {
      intVal = getchar() - '0';
      exponentPart = exponentPart * 10 + intVal;   
    } 
    //convert to float with exponent
    floatNo = floatNo / pow (10, (exponent + sign*exponentPart));
      
    if (floatNo > FLT_MAX || floatNo < FLT_MIN) 
    {
      printf("Floating number out of range\n");
      tok->tokentype = NUMBERTOK;
      tok->basicdt = REAL;
      tok->realval = floatNo;
      return tok;
    } 
    else 
    {
      tok->tokentype = NUMBERTOK;
      tok->basicdt = REAL;
      tok->realval = floatNo;
      return tok;
    }

  }

  if (isFloat) 
  {
    if (floatNo > FLT_MAX || floatNo < FLT_MIN) 
    {
      printf("Floating number out of range\n");
      tok->tokentype = NUMBERTOK;
      tok->basicdt = REAL;
      tok->realval = floatNo;
      return tok;
    } 
    else 
    {
      floatNo = floatNo / pow (10, exponent);
      tok->tokentype = NUMBERTOK;
      tok->basicdt = REAL;
      tok->realval = floatNo;
      return tok;
    }
  }

  if (intError) 
  {
    printf("Integer number out of range\n");
    tok->tokentype = NUMBERTOK; 
    tok->basicdt = INTEGER;
    tok->intval = (int)num;
    return (tok);     
  } 
  else 
  {
    tok->tokentype = NUMBERTOK; 
    tok->basicdt = INTEGER;
    tok->intval = num;
    return (tok);
  } 
}
