%{     /* pars1.y    Pascal Parser      Gordon S. Novak Jr.  ; 30 Jul 13   */


//PARAS ARORA - CS 375
//DUE ON 03/27/2017
//Why is this assignment so hard and confusing???

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

#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"
#include <float.h>
#include <stdbool.h>
#include <stdlib.h>
#include <limits.h> //for INT_MIN

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
/* Notes
    - idlist, vblock, varspecs, vargroup, type, simpletype, block taken from slide 129 of class notes
    - all other rules derived from Pascal grammar flowcharts (https://www.cs.utexas.edu/users/novak/grammar.html)
    - "$$ = $1" is implicit if no action specified according to yacc specs, but is explicit here for clarity
  */

  program     : 
          PROGRAM IDENTIFIER LPAREN idlist RPAREN SEMICOLON lblock DOT
                          { parseresult = makeprogram($2, $4, $7); }
            ;

    statement : 
            NUMBER COLON statement      { $$ = dolabel($1, $2, $3); }
          | assignment            { $$ = $1; }

          | IDENTIFIER LPAREN 
            argslist RPAREN         { $$ = makefuncall($2, $1, $3); }

            | BEGINBEGIN statement endpart    { $$ = makepnb($1, cons($2, $3)); }
            | IF expr THEN statement endif    { $$ = makeif($1, $2, $4, $5); }
            | WHILE expr DO statement     { $$ = makewhile($1, $2, $3, $4); }
            | REPEAT stmtlist UNTIL expr    { $$ = makerepeat($1, $2, $3, $4); }

            | FOR assignment TO expr 
              DO statement          { $$ = makefor(1, $1, $2, $3, $4, $5, $6); }

            | FOR assignment DOWNTO 
              expr DO statement       { $$ = makefor(-1, $1, $2, $3, $4, $5, $6); }

            | GOTO NUMBER           { $$ = dogoto($1, $2); }
            | /* empty */           { $$ = NULL; }
            ;

  stmtlist  : 
          statement SEMICOLON stmtlist    { $$ = cons($1, $3); }
        | statement             { $$ = $1; }
        ;

  idlist    : 
          IDENTIFIER COMMA idlist     { $$ = cons($1, $3); }
        | IDENTIFIER            { $$ = cons($1, NULL); }
        ;

  argslist  : 
          expr COMMA argslist       { $$ = cons($1, $3); }
        | expr                { $$ = cons($1, NULL); }
        ;

  lblock    : 
          LABEL llist SEMICOLON cblock    { $$ = $4; } // lblock -> cblock -> tblock -> vblock -> block
        | cblock              { $$ = $1; }
        ;

  cblock    : 
          CONST clist tblock        { $$ = $3; }
        | tblock              { $$ = $1; }
        ;

  tblock    : 
          TYPE tspecs vblock        { $$ = $3; }
        | vblock              { $$ = $1; }
        ;

  vblock    : 
          VAR varspecs block        { $$ = $3; }
        | block               { $$ = $1; }
        ;
  
  block   : 
          PROCEDURE IDENTIFIER paramlist 
          SEMICOLON block SEMICOLON   { $$ = $1; }

        | FUNCTION IDENTIFIER paramlist 
          COLON IDENTIFIER SEMICOLON 
          block SEMICOLON         { $$ = $1; }

        | BEGINBEGIN statement endpart    { $$ = makepnb($1, cons($2, $3)); }
        ;

  paramlist : 
          LPAREN paramgroup         { $$ = $1; }
        | /* empty */           { $$ = NULL; }
        ;

  paramgroup  : 
          idlist COLON IDENTIFIER RPAREN  { $$ = cons($1, $3); }

        | idlist COLON IDENTIFIER 
          SEMICOLON paramgroup      { $$ = cons($1, $3); }

        | FUNCTION idlist COLON 
          IDENTIFIER RPAREN       { $$ = cons($2, $4); }

        | FUNCTION idlist COLON IDENTIFIER
          SEMICOLON paramgroup      { $$ = cons($2, $4); }

        | VAR idlist COLON 
          IDENTIFIER RPAREN       { $$ = cons($2, $4); }

        | VAR idlist COLON IDENTIFIER 
          SEMICOLON paramgroup      { $$ = cons($2, $4); }

        | PROCEDURE idlist RPAREN     { $$ = $2; }
        | PROCEDURE idlist SEMICOLON 
          paramgroup            { $$ = $2; }
        ;

  llist   : 
          NUMBER COMMA llist        { instlabel($1); /* $$ = cons($1, $3); */ }
        | NUMBER              { instlabel($1); }
        ;

  clist   : 
          IDENTIFIER EQ NUMBER 
          SEMICOLON clist         { instconst($1, $3); }

        | IDENTIFIER EQ NUMBER SEMICOLON  { instconst($1, $3); }
        ;

  tspecs    : 
          tgroup SEMICOLON tspecs     { $$ = $3; }
        | tgroup SEMICOLON          { $$ = $1; }
        ; 

  tgroup    : 
          IDENTIFIER EQ type        { insttype($1, $3); }
        ;

  varspecs  : 
          vargroup SEMICOLON varspecs   { $$ = $3; }
        | vargroup SEMICOLON        { $$ = $1; }
        ;

  vargroup  : 
          idlist COLON type         { instvars($1, $3); }
        ;

    endpart   : 
            SEMICOLON statement endpart     { $$ = cons($2, $3); }
            | END                             { $$ = NULL; }
            ;
             
    endif   : 
            ELSE statement                  { $$ = $2; }
            | /* empty */                     { $$ = NULL; }
            ;

    assignment  : 
            factor ASSIGN expr            { $$ = binop($2, $1, $3); }
          ;

    var     : 
            IDENTIFIER            { $$ = findid($1); }
          | var DOT IDENTIFIER        { $$ = reducedot($1, $2, $3); }
          | mergebracks
          | var POINT             { $$ = dopoint($1, $2); }
          ;

    mergebracks :
            IDENTIFIER mergelist        { $$ = arrayref($1, NULL, $2, NULL); }
          ;

    mergelist :
            LBRACKET argslist RBRACKET    { $$ = $2; }

          | LBRACKET argslist 
            RBRACKET mergelist        { $$ = nconc($2, $4); }
          ;

  fieldlist : 
          idlist COLON type         { instfields($1, $3); }

        | idlist COLON type 
          SEMICOLON fieldlist       { instfields($1, $3); $$ = nconc($1, $5); }
        
        | /* empty */           { $$ = NULL; }
        ;
        
  type    : 
          simpletype            { $$ = $1; }
        | POINT IDENTIFIER          { $$ = instpoint($1, $2); }

        | ARRAY LBRACKET simplelist 
          RBRACKET OF type        { $$ = instarray($3, $6); }

        | RECORD fieldlist END        { $$ = instrec($1, $2); }
        ;

  simpletype  : 
          IDENTIFIER            { $$ = findtype($1); }
        | LPAREN idlist RPAREN        { $$ = instenum($2); }
        | NUMBER DOTDOT NUMBER        { $$ = instdotdot($1, $2, $3); }
        ;

  simplelist  : 
          simpletype COMMA simplelist   { $$ = cons($3, $1); } // $$ = cons($1, $3);
        | simpletype            { $$ = $1; }
        ;
         
    expr    : 
            simpexpr EQ simpexpr        { $$ = binop($2, $1, $3); }
          | simpexpr LT simpexpr        { $$ = binop($2, $1, $3); }
            | simpexpr GT simpexpr        { $$ = binop($2, $1, $3); }
            | simpexpr NE simpexpr        { $$ = binop($2, $1, $3); }
            | simpexpr LE simpexpr        { $$ = binop($2, $1, $3); }
            | simpexpr GE simpexpr        { $$ = binop($2, $1, $3); }
            | simpexpr IN simpexpr        { $$ = binop($2, $1, $3); }
            | simpexpr              { $$ = $1; }
            ;

  simpexpr  : 
          unaryexpr PLUS term       { $$ = binop($2, $1, $3); }
        | unaryexpr MINUS term        { $$ = binop($2, $1, $3); }
        | unaryexpr OR term         { $$ = binop($2, $1, $3); }
        | unaryexpr             { $$ = $1; }
        ;

  unaryexpr : 
          PLUS term             { $$ = unaryop($1, $2); }
        | MINUS term            { $$ = unaryop($1, $2); }
        | term                { $$ = $1; }
        ;
    
    term    : 
            factor TIMES factor               { $$ = binop($2, $1, $3); }
          | factor DIVIDE factor              { $$ = binop($2, $1, $3); }
          | factor DIV factor               { $$ = binop($2, $1, $3); }
          | factor MOD factor               { $$ = binop($2, $1, $3); }
          | factor AND factor               { $$ = binop($2, $1, $3); }
            | factor              { $$ = $1; }
            ;
             
    factor    : 
            NUMBER              { $$ = $1; }
          | var               { $$ = $1; }
          | IDENTIFIER LPAREN argslist RPAREN { $$ = makefuncall($2, $1, $3); }
          | LPAREN expr RPAREN              { $$ = $2; }
          | NOT factor            { $$ = unaryop($1, $2); }
            | LBRACKET factorlist RBRACKET    { $$ = $2; }
            | STRING              { $$ = $1; }
            | NIL               { $$ = $1; }
            ;

  factorlist  :
          expr                { $$ = $1; }
        | expr DOTDOT expr          { $$ = instdotdot($1, $2, $3); }
        | expr DOTDOT expr COMMA factorlist { $$ = instdotdot($1, $2, $3); }
        | /* empty */           { $$ = NULL; }
;

%%



#define NUM_COERCE_IMPLICIT 1

#define ELIM_NESTED_PROGN   1   /* disables makepnb() functionality and defaults to makeprogn() if 0 */

#define DEBUG_MASTER_SWITCH 1   /* 1 for true, 0 for false  */

/* See parse.h for all debug constants */

 int arrForLabel[100];
 int labelnumber = 0;  /* sequential counter for internal label numbers */

 char *last_method = "makeprogram()";

/* addoffs adds offset, off, to an aref expression, exp */
TOKEN addoffs(TOKEN exp, TOKEN off) {


  exp = addint(exp, off, NULL);

  
  return exp;
}

TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb) {
  int up = 0;
  SYMBOL to, what, holder, togeth[10];
  TOKEN point = NULL;

  to = searchst(arr->stringval);
  holder = to->datatype;

  for(; (holder->kind != 8) && holder; ) { //TYPESYM
    togeth[up] = holder;
    up++;
    holder = holder->datatype;
  }

  what = holder;
  if(subs->tokentype == 5 && subs->link == NULL) { //NUMBERTOK
    int sum = (subs->whichval - 1) * what->size;
    point = makearef(arr, makeintc(sum), NULL);
    point->datatype = to->basicdt;
    return point;
  }

  TOKEN sub2 = subs;
  up = 0;

  while(sub2) {
    if(up != 0) {
      if(sub2->tokentype == 5) //NUMBERTOK
        point->operands->link->operands = addint(point->operands->link->operands, makeintc(sub2->whichval * what->size), NULL);
      else {
        SYMBOL yep = togeth[up];
        int length = yep->size / (yep->highbound - yep->lowbound + 1);
        TOKEN func1, func2, func3, func4, func5;
        func1 = makeop(3); //TIMESOP
        func2 = makeintc(length);
        func3 = makeintc(length * -1); 

        func1->operands = func2;
        func2->link = sub2;
        point->operands->link->operands = addint(point->operands->link->operands, func3, NULL);

        func4 = point->operands->link->operands->link;
        func5 = makeplus(func4, func1, NULL);
        point->operands->link->operands->link = func5;

      }
    }
    else {
      SYMBOL yep = togeth[up];
      int length = yep->size / (yep->highbound - yep->lowbound + 1);
      TOKEN func1, func2, func3, func4;
      func1 = makeop(3); //TIMESOP
      func2 = makeintc(length);
      func3 = makeintc(length * -1);

      func1->operands = func2;
      func2->link = sub2;
      func3->link = func1;

      func4 = makeplus(func3, func1, NULL);

      point = makearef(arr, func4, NULL);
      point->datatype = to->basicdt;
    }
    TOKEN sub3 = sub2;
    sub2 = sub2->link;
    sub3->link = NULL;
    up++;
  }
  return point;
}

TOKEN dopoint(TOKEN var, TOKEN tok) {
  tok->operands = var;
  return tok;
}

TOKEN instarray(TOKEN bounds, TOKEN typetok) {
  int down;
  SYMBOL symba = NULL;
  int up;
  TOKEN yes = bounds;
  SYMBOL next = searchst(typetok->stringval);

  for(; yes; yes = yes->link) {
    SYMBOL other = symalloc();
    other->kind = 6; //ARRAYSYM
    if(!next)
      other->basicdt = typetok->datatype;
    else
      other->datatype = next;
    down = yes->symtype->lowbound;
    up = yes->symtype->highbound;
    if(symba) {
      other->datatype = typetok->symtype;
      other->size = (up - down + 1) * symba->size;
    }
    else
      other->size = (up - down + 1) * next->size;

    typetok->symtype = other;
    symba = other;
    other->highbound = up;
    other->lowbound = down;
  }
  return typetok;
}

TOKEN instdotdot(TOKEN lowtok, TOKEN dottok, TOKEN hightok) {
  return (makesubrange(dottok, lowtok->intval, hightok->intval));
}

TOKEN instenum(TOKEN idlist) {
  TOKEN yes;
  int length = 0;
  yes = idlist;
  TOKEN go;
  for(; yes; yes = yes->link) {
    instconst(yes, makeintc(length));
    length++;
  }
  go = makesubrange(idlist, 0, (length - 1));
  return go;
}

TOKEN instfields(TOKEN idlist, TOKEN typetok) {
  SYMBOL symba, symba2;
  int up = 0, down = 0;
  TOKEN yes = idlist;
  for(; yes; yes = yes->link) {
    symba2 = searchst(typetok->stringval);
    symba = makesym(yes->stringval);
    symba->datatype = symba2;
    down = up;
    up = up + symba2->size;
    symba->offset = down;
    symba->size = symba2->size;
    symba->datatype = symba2;
    if(symba2->kind == 1) { //BASICTYPE
      symba->basicdt = symba2->basicdt;
    }
    yes->symtype = symba;
  }
  return idlist;
}

TOKEN instpoint(TOKEN tok, TOKEN typename) {
  SYMBOL back, symba;
  back = symalloc();
  back->kind = 9; //POINTERSYM
  back->basicdt = 4; //POINTER
  back->size = basicsizes[4]; //POINTER
  tok->symtype = back;

  symba = searchins(typename->stringval);
  symba->kind = 8; //TYPESYM
  back->datatype = symba;
  tok->datatype = 4; //POINTER
  return tok;
}

TOKEN instrec(TOKEN rectok, TOKEN argstok) {
  SYMBOL symba = symalloc();
  TOKEN yes;
  int full, next;
  TOKEN goOn;
  symba->kind = 7; //RECORDSYM
  rectok->symtype = symba;
  symba->datatype = argstok->symtype;
  next = wordaddress(argstok->symtype->size, 8);
  full = next;

  yes = argstok;
  goOn = argstok->link;

  for (; goOn; goOn = goOn->link) {
    yes->symtype->link = goOn->symtype;
    next = wordaddress(goOn->symtype->size, 8);   
    goOn->symtype->offset = full;
    full = full + next;

    yes = goOn;
  }
  symba->size = full;
  return rectok;
}

void insttype(TOKEN typename, TOKEN typetok) {
  SYMBOL symba, next;
  next = typetok->symtype;
  symba = searchins(typename->stringval);
  symba->kind = 8; //TYPESYM
  symba->size = next->size;
  symba->datatype = next;
  symba->basicdt = next->basicdt;
}

TOKEN makearef(TOKEN var, TOKEN off, TOKEN tok) {
  TOKEN yes;
  yes = makeop(25); //AREFOP
  yes->operands = var;
  var->link = off;
  return yes;
}

TOKEN makesubrange(TOKEN tok, int low, int high) {
  SYMBOL symba;
  TOKEN yes = copytok(tok);
  symba = symalloc();
  symba->size = basicsizes[0]; //INTEGER
  symba->lowbound = low;
  symba->kind = 4; //SUBRANGE
  symba->highbound = high;
  symba->basicdt = 0; //INTEGER
  yes->symtype = symba;
  return yes;
}

TOKEN nconc(TOKEN lista, TOKEN listb) {
  TOKEN yes;
  yes = lista;
  for(; yes->link != NULL; )
    yes = yes->link;
  yes->link = listb;
  return lista;
}

//last token thru the link
TOKEN lastyLastLink(TOKEN tok) {
  TOKEN un = tok;
  TOKEN next = un->link;
  for(; next; ) {
    un = next;
    next = next->link;
  }
  return un;
}

//last token connected
TOKEN lastyLastOp(TOKEN tok) {
  TOKEN here;
  TOKEN there;
  if(!tok) {
    printf("THIS IS THE PROBLEM 2\n\n\n");
    return NULL;
  }
    
  here = tok;
  there = here->operands;
  for(; there; there = there->operands)
    here = there;
  return here;
}

TOKEN balanceHelp(float f) {
  TOKEN yes;
  yes = talloc();
  yes->tokentype = 5; //NUMBERTOK
  yes->datatype = 1; //REAL
  yes->realval = f;
  return yes;
}

TOKEN balance(TOKEN go, TOKEN on) {
  bool no = 0;
  SYMBOL holder;
  TOKEN make;
  SYMBOL symba = NULL;
  TOKEN make2;
  SYMBOL symba2;
  TOKEN make3;
  make = makeintc(-1);
  make2 = lastyLastOp(go);
  make3 = lastyLastLink(go->operands);
  symba2 = searchst(make2->stringval);

  if(go->whichval == 25) //AREFOP
    no = 1;

  holder = symba2;
  for(; holder; holder = holder->datatype) {
    if(holder->datatype->kind == 1) //BASICTYPE
      break;
  }
  for(; holder; holder = holder->link) {
    if((holder->offset == make3->whichval) && no) {
      symba = holder;
      break;
    }
    else if((strcmp(holder->namestring, on->stringval) == 0)) {
      symba = holder;
      if(!no) {
        make->whichval = symba->offset;
        if(symba->datatype->basicdt == 1) { //REAL
          make->link = balanceHelp(0);
          make->link->realval = -DBL_MAX;
        }
      }
      else {
        if(make3->tokentype == 0) //OPERATOR
          make->whichval = -1;
        else
          make->whichval = make3->whichval + symba->offset;
        if(symba->datatype->basicdt == 1) { //REAL
          make->link = balanceHelp(0);
          make->link->realval = -DBL_MAX;
        }
      }
      return make;
    }
  }
  if(symba && no) {
    SYMBOL symH = searchst(symba->datatype->namestring);
    symba = NULL;
    for(; symH; symH = symH->datatype) {
      if(symH->datatype->kind == 1 && symH->datatype) //BASICTYPE
        break;
    }
    while(!symba && symH) {
      if(strcmp(symH->namestring, on->stringval) == 0)
        symba = symH;
      else
        symH = symH->link;
    }
    if(symba) {
      make->whichval = make3->whichval + symba->offset;
      if(symba->datatype->basicdt == 1) { //REAL
        make->link = balanceHelp(0);
        make->link->realval = -DBL_MAX;
      }
      return make;
    }
  }
  else if(symba && !no) {
    make->whichval = symba->offset;
    if(symba->datatype->basicdt == 1) { //REAL
      make->link = balanceHelp(0);
      make->link->realval = -DBL_MAX;
    }
    return make;
  }
  return make;
}

/* reducedot handles a record reference.
   dot is a (now) unused token that is recycled. */
TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {


  TOKEN aref;
  TOKEN offset = balance(var, field);

  if (var->whichval == AREFOP) {
    /* Avoid adding multiple copies to the tree. */

    if (offset->whichval >= 0) {
      var->operands->link = offset;
    }
    aref = var;
  }
  else {
    aref = makearef(var, offset, NULL);
  }

  /* Change aref's datatype to REAL to avoid incorrect
     fixes/floats in binop(). NULL out the dummy link. */
  if (offset->link && offset->link->datatype == REAL &&
    offset->link->realval == -DBL_MAX) {

    aref->datatype = REAL;
    offset->link = NULL;
  }
  

  return aref;
}

/* ############################################################################################################################################################### */

/* addint adds integer off to expression exp, possibly using tok */
TOKEN addint(TOKEN exp, TOKEN off, TOKEN tok) {
  if (!exp || !off) {
    return NULL;
  }

  int a = exp->intval;
  int b = off->intval;
  

  if ((b > 0) && (a > INT_MAX - b)) { // if ((INT_MAX / exp->intval) > off->intval)
    printf(" Error: integer overflow detected, addint()\n");
    printf(" Cannot add %d to %d\n", b, a);
  }
  else {
    exp->intval = a + b;
  }
  
  return exp;
}

/* This method fixes or floats a NUMBERTOK as necessary. */
TOKEN binop_type_coerce(TOKEN op, TOKEN lhs, TOKEN rhs) {

  TOKEN cast_tok;

  int lhs_datatype = lhs->datatype;
  int rhs_datatype = rhs->datatype;
  int op_type = op->whichval;

  if (lhs_datatype == INTEGER && rhs_datatype == REAL) {
    /* LHS is integer, RHS is real.
       Fix if ASSIGNOP, else float the integer. */

    op->datatype = REAL;

    if (op_type == ASSIGNOP) {
      cast_tok = makefix(rhs);
      op->operands = lhs;
      lhs->link = cast_tok;
    }
    else {
      cast_tok = makefloat(lhs);
      op->operands = cast_tok;
      cast_tok->link = rhs;
    }

  }
  else if (lhs_datatype == REAL && rhs_datatype == INTEGER) {
    /* LHS is real, RHS is integer.
       Float the integer value.
       DO NOT fix; lhs still takes precedence. */

    cast_tok = makefloat(rhs);

    op->datatype = REAL;
    op->operands = lhs;
    lhs->link = cast_tok;
    cast_tok->link = NULL;
    rhs->link = NULL;

  }
  else {
    op->datatype = lhs->datatype;
    op->operands = lhs;   // link operands to operator
    lhs->link = rhs;    // link second operand to first
    rhs->link = NULL;   // terminate operand list
  }

  return op;
}

/* binop links a binary operator op to two operands, lhs and rhs.

   TODO
   - boolean types?
   - funcall return types?
*/
TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs) {

  /* If rhs represents nil, convert rhs to
     an INTEGER NUMBERTOK with ->whichval = 0. */
  if (rhs->whichval == (NIL - RESERVED_BIAS)) {
    rhs->tokentype = NUMBERTOK;
    rhs->datatype = INTEGER;
    rhs->whichval = 0;
  }

  int lhs_datatype = lhs->datatype;
  int rhs_datatype = rhs->datatype;
  int op_type = op->whichval;

  /* Type checking/coercion needed. */
  if (lhs_datatype != rhs_datatype) {
    op = binop_type_coerce(op, lhs, rhs);
  }
  else {
    op->datatype = lhs->datatype;
    op->operands = lhs;   // link operands to operator
    lhs->link = rhs;    // link second operand to first
    rhs->link = NULL;   // terminate operand list
  }


  return op;
}

/* cons links a new item onto the front of a list.  Equivalent to a push.
   (cons 'a '(b c))  =  (a b c) */
TOKEN cons(TOKEN item, TOKEN list) {


  item->link = list;


  return item;
}

/* copytok makes a new token that is a copy of origtok */
TOKEN copytok(TOKEN origtok) {


  if (!origtok) {
    return NULL;
  }
  TOKEN out = talloc();


  out->tokentype = origtok->tokentype;
  out->datatype = origtok->datatype;

  /* Shallow copies only (as expected). */
  out->symtype = origtok->symtype;
  out->symentry = origtok->symentry;
  out->operands = origtok->operands;
  out->link = origtok->link;
  
  if (origtok->stringval[0] != '\0') {
    strncpy(out->stringval, origtok->stringval, 16);
  }
  else if (origtok->whichval != -1) {
    out->whichval = origtok->whichval;
  }
  else if (origtok->realval != -DBL_MIN) {
    out->realval = origtok->realval;
  }
  else {
    out->intval = origtok->intval;
  }


  return out;
}

int labelForMe(int a) {
  int b = 0;
  while(b < 100) {
    if(arrForLabel[b] == a) {
      //printf("LABEL NUMBER %d-%d\n", b, external_label_num);
      return b;
    }
    b++;
  }
  return -1;
}

/* dogoto is the action for a goto statement.
   tok is a (now) unused token that is recycled. */
TOKEN dogoto(TOKEN tok, TOKEN labeltok) {

  // THIS METHOD SHOULD ONLY BE CALLED FOR A USER LABEL




  int internal_label_num = labelForMe(labeltok->intval);
 
  


  return (makegoto(internal_label_num));
}

/* dolabel is the action for a label of the form   <number>: <statement>
   tok is a (now) unused token that is recycled. */
TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement) {


  
  int internal_label_num = labelForMe(labeltok->intval);


  TOKEN do_progn_tok = makeop(PROGNOP);
  TOKEN label_tok = makeop(LABELOP);
//  TOKEN do_progn_tok = makeprogn(makeop(PROGNOP), makeop(LABELOP)); // second arg will never be progn, so skip makepnb()
  TOKEN label_num_tok = makeintc(internal_label_num);



  do_progn_tok->operands = label_tok;
  label_tok->operands = label_num_tok;
  label_tok->link = statement;



  return do_progn_tok;
}

/* findid finds an identifier in the symbol table, sets up symbol table\n
   pointers, changes a constant to its number equivalent

   Adapted from Prof. Novak's class notes with permission. */
TOKEN findid(TOKEN tok) {


  SYMBOL sym, typ;
  sym = searchst(tok->stringval);

  if (sym->kind == CONSTSYM) {
  
    tok->tokentype = NUMBERTOK;

    if (sym->basicdt == 0) {
      tok->datatype = INTEGER;
      tok->intval = sym->constval.intnum;
    }
    else if (sym->basicdt == 1) {
      tok->datatype = REAL;
      tok->realval = sym->constval.realnum;
    }

  }
  else {
  
    tok->symentry = sym;
    typ = sym->datatype;
    tok->symtype = typ;

    if (typ->kind == BASICTYPE || typ->kind == POINTERSYM) {
      tok->datatype = typ->basicdt;
    }

  }


  return tok;
}

/* findtype looks up a type name in the symbol table, puts the pointer
   to its type into tok->symtype, returns tok. */
TOKEN findtype(TOKEN tok) {

  
  SYMBOL sym, typ;
//  sym = searchins(tok->stringval);
  sym = searchst(tok->stringval);


  typ = sym->datatype;
  int kind = sym->kind;

  /* Arg represents symbol of basic datatype (INTEGER, REAL, STRINGTYPE, BOOLETYPE, POINTER) */
  if (kind == BASICTYPE) {
    tok->datatype = sym->basicdt;
    tok->symtype = sym;
  }
  else {
    tok->symtype = typ;
  }


  return tok;
}

/* instconst installs a constant in the symbol table */
void instconst(TOKEN idtok, TOKEN consttok) {


  SYMBOL sym;

  sym = insertsym(idtok->stringval);
  sym->kind = CONSTSYM;
  sym->basicdt = consttok->datatype;

  if (sym->basicdt == INTEGER) {    // INTEGER
    sym->constval.intnum = consttok->intval;
    sym->size = basicsizes[INTEGER];  // 4
  }
  else if (sym->basicdt == REAL) {  // REAL
    sym->constval.realnum = consttok->realval;
    sym->size = basicsizes[REAL]; // 8
  }
  else if (sym->basicdt == STRINGTYPE) {
    strncpy(sym->constval.stringconst, consttok->stringval, 16);
    sym->size = basicsizes[STRINGTYPE];
  }


}

void instlabel (TOKEN num) {
  arrForLabel[labelnumber++] == num->intval;
}

/* instvars will install variables in symbol table.
   typetok is a token containing symbol table pointer for type.

   Note that initsyms() is already called in main().

   Adapted from Prof. Novak's class notes with permission. */
void instvars(TOKEN idlist, TOKEN typetok) {

  SYMBOL sym, typesym;
  int align;

  typesym = typetok->symtype;
  align = alignsize(typesym);

  while (idlist != NULL) {
    sym = insertsym(idlist->stringval);
    sym->kind = VARSYM;
    sym->offset = wordaddress(blockoffs[blocknumber], align);
    sym->size = typesym->size;
    blockoffs[blocknumber] = sym->offset + sym->size;
    sym->datatype = typesym;
    sym->basicdt = typesym->basicdt;

    if (typesym->datatype != NULL && typesym->datatype->kind == ARRAYSYM) {
      SYMBOL arr_type = typesym->datatype;
      while (arr_type && arr_type->kind == ARRAYSYM) {
        arr_type = arr_type->datatype;
      }
      if (arr_type->kind == BASICTYPE) {
        sym->basicdt = arr_type->basicdt;
      }
    }

    
    idlist = idlist->link;
  }

}

/* makefix forces the item tok to be integer, by truncating a constant
   or by inserting a FIXOP operator */
TOKEN makefix(TOKEN tok) {


  TOKEN out = makeop(FIXOP);  // create FIXOP TOKEN


  out->operands = tok;
  out->link = NULL;


  return out;
}

/* makefloat forces the item tok to be floating, by floating a constant
   or by inserting a FLOATOP operator */
TOKEN makefloat(TOKEN tok) {


  TOKEN out;

  if (NUM_COERCE_IMPLICIT && tok->tokentype == NUMBERTOK) {
    /* e.g., floating 34 prints "3.400000e+01" to console */
    out = tok;
    out->datatype = REAL;
    out->realval = out->intval;
    out->intval = INT_MIN;
  }
  else {
    /* e.g., floating 34 prints "(float 34)" to console */
    out = makeop(FLOATOP);
    

    out->operands = tok;
    out->link = NULL; 
  }



  return out;
}

/* A helper method used to create the TOKENs required to increment
   the counter var in a for-loop.

   Returned TOKENs are of the form "(:= i (+ i 1))".  */
TOKEN makeloopincr(TOKEN var, int incr_amt) {
  // if in makefor(), send in asg->operands

  TOKEN assignop = makeop(ASSIGNOP);
  TOKEN var_cpy = copytok(var);
  TOKEN plusop = makeplus(copytok(var), makeintc(incr_amt), NULL);  // PLUSOP operand "var" link amt

  assignop->operands = var_cpy;
  var_cpy->link = plusop;

  return assignop;
}

/* makefor makes structures for a for statement. sign == 1 for regular
   for-loop, -1 for downto for-loop. tok, tokb and tokc are (now) unused
   tokens that are recycled. */
TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, 
      TOKEN endexpr, TOKEN tokc, TOKEN statement) {

 

  TOKEN for_asg_progn_tok = makepnb(talloc(), asg);
  TOKEN label_tok = makelabel();
  
  TOKEN stop_op_tok = makeop(LEOP);
  TOKEN do_progn_tok = makepnb(talloc(), statement);
  TOKEN ifop_tok = makeif(makeop(IFOP), stop_op_tok, do_progn_tok, NULL);

  TOKEN loop_stop_tok = copytok(asg->operands); // the counter var, eg "i" in trivb.pas
  TOKEN stmt_incr_tok = makeloopincr(asg->operands, sign);
  TOKEN goto_tok;



  goto_tok = makegoto(label_tok->operands->intval); // not null-checked

  if (sign == -1) {
    stop_op_tok->whichval = GEOP; // "downto"
  }

  /* Link all the tokens together. */
  asg->link = label_tok;
  label_tok->link = ifop_tok;
  stop_op_tok->operands = loop_stop_tok;
  loop_stop_tok->link = endexpr;

  /* Handle elimination of nested progns */
  if (do_progn_tok->whichval != PROGNOP) {
    do_progn_tok->operands = statement;
    statement->link = stmt_incr_tok;
  }
  else {  // do_progn_tok == statement
    lastyLastLink(do_progn_tok->operands)->link = stmt_incr_tok;
  }
  stmt_incr_tok->link = goto_tok;


  return for_asg_progn_tok;
}


// assumes fn is always a write() or writeln() function
// does not do cross-conversions (e.g., send in writelnf() to convert to writelni())
// identifier datatypes?
TOKEN write_fxn_args_type_check(TOKEN fn, TOKEN args) {

  if (args->datatype == STRINGTYPE) {
    return fn;
  }

  TOKEN out = NULL;

  SYMBOL fn_sym = searchst(fn->stringval);


  int fn_arg_type = fn_sym->datatype->link->basicdt;
  int args_type = args->datatype;

  if (args_type == STRINGTYPE) {
    out = fn;
  }
  else {

    int replace_index = 5;
    if (strcmp(fn->stringval, "writeln") == 0) {
      replace_index = 7;
    }

    if (strcmp(fn->stringval, "write") == 0) {

      if (args_type == INTEGER) {
        fn->stringval[replace_index] = 'i';
        fn->stringval[replace_index + 1] = '\0';
        out = fn;
      }
      else if (args_type == REAL) {
        fn->stringval[replace_index] = 'f';
        fn->stringval[replace_index + 1] = '\0';
        out = fn;       
      }

    }
    else if (strcmp(fn->stringval, "writeln") == 0) {

      if (args_type == INTEGER) {
        fn->stringval[replace_index] = 'i';
        fn->stringval[replace_index + 1] = '\0';
        out = fn;
      }
      else if (args_type == REAL) {
        fn->stringval[replace_index] = 'f';
        fn->stringval[replace_index + 1] = '\0';
        out = fn;
      }

    }
  }

  return out;
}
      
/* makefuncall makes a FUNCALL operator and links it to the fn and args.
   tok is a (now) unused token that is recycled. */
TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) {

  TOKEN funcall_tok;

  if (strcmp(fn->stringval, "new") != 0) {

    funcall_tok = makeop(FUNCALLOP);    // 24


    SYMBOL this_fxn = searchst(fn->stringval);

    
    funcall_tok->datatype = this_fxn->datatype->basicdt;

    if (strcmp(fn->stringval, "write") == 0 || strcmp(fn->stringval, "writeln") == 0) {
      fn = write_fxn_args_type_check(fn, args);
      if (!fn) {
        return NULL;
      }
    }

    /* (+ i j) => +->operands = i and i->link = j; (funcall_tok fn args) */
    funcall_tok->operands = fn;
    fn->link = args;
  }
  else {
    funcall_tok = makeop(ASSIGNOP);
    TOKEN funcall = makeop(FUNCALLOP);

    SYMBOL this_type = searchst(args->stringval);



    funcall_tok->operands = args;
    args->link = funcall;
    funcall->operands = fn;
    fn->link = makeintc(this_type->datatype->datatype->datatype->size);

  }


  return funcall_tok;
}



/* makegoto makes a GOTO operator to go to the specified label.
   The label number is put into a number token. */
TOKEN makegoto(int label) {


  TOKEN goto_tok = makeop(GOTOOP);
  TOKEN goto_num_tok = makeintc(label);

  goto_tok->operands = goto_num_tok;  // operand together


  return goto_tok;
}

/* makeif makes an IF operator and links it to its arguments.
   tok is a (now) unused token that is recycled to become an IFOP operator */
TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart) {

  
  tok->tokentype = OPERATOR;  /* Make it look like an operator. */
  tok->whichval = IFOP;
  
  if (elsepart != NULL) {
    elsepart->link = NULL;
  }

  thenpart->link = elsepart;
  exp->link = thenpart;
  tok->operands = exp;


  return tok;
}

/* makeintc makes a new token with num as its value */
TOKEN makeintc(int num) {


  TOKEN out = talloc();


  out->tokentype = NUMBERTOK;
  out->datatype = INTEGER;
  out->intval = num;


  return out;
}

/* makelabel makes a new label, using labelnumber++ */
TOKEN makelabel() {

  TOKEN label_tok = makeop(LABELOP);
  TOKEN label_num_tok = makeintc(labelnumber++);  // increment it after creation


  label_tok->operands = label_num_tok;  // operand together


  return label_tok;
}


/* makeop makes a new operator token with operator number opnum.
   Example:  makeop(FLOATOP)  */
TOKEN makeop(int opnum) {




  TOKEN out = talloc();


  out->tokentype = OPERATOR;
  out->whichval = opnum;


  return out;
}

/* makeplus makes a + operator.
   tok (if not NULL) is a (now) unused token that is recycled. */
TOKEN makeplus(TOKEN lhs, TOKEN rhs, TOKEN tok) {


  TOKEN out = makeop(PLUSOP);
  if (lhs && rhs) {
    out->operands = lhs;
    lhs->link = rhs;
    rhs->link = NULL;
  }


  return out;
}

TOKEN maketimes(TOKEN lhs, TOKEN rhs, TOKEN tok) {

  TOKEN out = makeop(TIMESOP);
  if (lhs && rhs) {
    out->operands = lhs;
    lhs->link = rhs;
    rhs->link = NULL;
  }

  return out;
}

/* makepnb is like makeprogn, except that if statements is already a progn,
   it just returns statements.  This is optional. */
TOKEN makepnb(TOKEN tok, TOKEN statements) {

  if (statements->whichval == PROGNOP && ELIM_NESTED_PROGN) {
    return statements;
  }

  return (makeprogn(tok, statements));
}

/* makeprogn makes a PROGN operator and links it to the list of statements.
   tok is a (now) unused token that is recycled. */
TOKEN makeprogn(TOKEN tok, TOKEN statements) {


  tok->tokentype = OPERATOR;    // 0
  tok->whichval = PROGNOP;    // 22
  tok->operands = statements;


  return tok;
}

/* makeprogram makes the tree structures for the top-level program */
TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements) {


  TOKEN program_start = makeop(PROGRAMOP);    // 26
  TOKEN progn_start = makepnb(talloc(), args);  // set []->operands to args
 

  /* Create the head of the tree (this is stored in parseresult). */
  program_start->operands = name;
  progn_start->link = statements;
  name->link = progn_start;


  return program_start;
}

/* makerepeat makes structures for a repeat statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr) {


  TOKEN label_tok = makelabel();
  TOKEN goto_tok = makegoto(label_tok->operands->intval);
  TOKEN rpt_progn_tok = makepnb(talloc(), label_tok); // operand label_tok to rpt_progn_tok
  TOKEN do_progn_tok = makeop(PROGNOP);
  TOKEN ifop_tok = makeif(makeop(IFOP), expr, do_progn_tok, NULL);


  /* Link TOKENs together */
  label_tok->link = statements;
  do_progn_tok->link = goto_tok;

  /* Handle elimination of nested progns */
  lastyLastLink(statements)->link = ifop_tok;


  return rpt_progn_tok;
}

/* makewhile makes structures for a while statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement) {


  if (expr->operands->link && expr->operands->link->whichval == (NIL - RESERVED_BIAS)) {
    expr->operands->link->tokentype = NUMBERTOK;
    expr->operands->link->datatype = INTEGER;
    expr->operands->link->whichval = 0;
  }

  TOKEN label_tok = makelabel();
  TOKEN goto_tok = makegoto(label_tok->operands->intval);
  TOKEN while_progn_tok = makepnb(talloc(), label_tok); // operand label_tok to while_progn_tok
  TOKEN do_progn_tok = makepnb(talloc(), statement);    // operand statement to do_progn_tok
  TOKEN ifop_tok = makeif(makeop(IFOP), expr, do_progn_tok, NULL);


  label_tok->link = ifop_tok;

  /* Handle elimination of nested progns */
  if (do_progn_tok->whichval != PROGNOP) {
    do_progn_tok->operands = statement;
    statement->link = goto_tok;
  }
  else {  // do_progn_tok == statement
    lastyLastLink(do_progn_tok->operands)->link = goto_tok;
  }


  return while_progn_tok;
}

/* mulint multiplies expression exp by integer n */
TOKEN mulint(TOKEN exp, int n) {
  if (!exp) {
    return NULL;
  }

  if (exp->datatype == INTEGER) {

    int a = exp->intval;
    int val = a * n;

    if (a != 0 && (a * n) / a != n) {
      printf(" Integer overflow detected, mulint()\n");
      printf(" Cannot multiply %d to %d\n", n, a);
    }
    else {
      exp->intval = val;
    }

  }
  else if (exp->datatype == REAL) {

  
    double val = exp->realval * n;

    if ((val > FLT_MAX || val < FLT_MIN)) {
      printf(" Floating number out of range, mulint()\n");
      printf(" Cannot multiply %d to %f\n", n, exp->realval);
    }
    else {
      exp->realval = val;
    }

  }

  return exp;
}

/* searchins will search for symbol, inserting it if not present. */
SYMBOL searchinsst(char name[]) {
  return (searchins(name));
}

/* settoktype sets up the type fields of token tok.
   typ = type pointer, ent = symbol table entry of the variable  */
void settoktype(TOKEN tok, SYMBOL typ, SYMBOL ent) {
  if (!tok || !typ || !ent) {
    // something;
  }

  tok->symtype = typ;
  tok->symentry = ent;
}

/* unaryop links a unary operator op to one operand, lhs. +/-/NOT */
TOKEN unaryop(TOKEN op, TOKEN lhs) {
  op->operands = lhs;
  lhs->link = NULL;
  return op;
}

/* wordaddress pads the offset n to be a multiple of wordsize.
   wordsize should be 4 for integer, 8 for real and pointers,
   16 for records and arrays */
int wordaddress(int n, int wordsize) { 
  return ((n + wordsize - 1) / wordsize) * wordsize;
}

yyerror(s) char *s; {
  fputs(s, stderr);
  putc('\n', stderr);
}

main()
  { int res;
    initsyms();
    res = yyparse();
    printst();
    printf("yyparse result = %8d\n", res);
    //if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
  }