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

 int arrForLabel[100];
 int labelnumber = 0;  /* sequential counter for internal label numbers */

    /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */

void  instvars(TOKEN idlist, TOKEN typetok) {
  SYMBOL sym, typesym; int align;
  /*if (DEBUG)
  { printf("instvars\n");
    dbugprinttok(idlist);
    dbugprinttok(typetok);
  }*/
  typesym = typetok->symtype;
  align = alignsize(typesym);
  while ( idlist != NULL )   /* for each id */
    {  sym = insertsym(idlist->stringval);
       sym->kind = VARSYM;
       sym->offset = wordaddress(blockoffs[blocknumber], align);
       sym->size = typesym->size;
       blockoffs[blocknumber] = sym->offset + sym->size;
       sym->datatype = typesym;
       sym->basicdt = typesym->basicdt; /* some student programs use this */
       idlist = idlist->link;
    };
  if (DEBUG) printst();
}

TOKEN makeintc(int num) {
  TOKEN yes = talloc();
  yes->tokentype = 5; //NUMBERTOK
  yes->datatype = 0; //INTEGER
  yes->intval = num;
  return yes;
}

TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr,
              TOKEN tokc, TOKEN statement) {
  TOKEN make = makepnb(talloc(), asg);
  TOKEN make2 = makelabel();
  TOKEN make3;
  TOKEN make4;
  TOKEN make5 = makepnb(talloc(), statement);
  TOKEN make6;
  TOKEN copy = copytok(asg->operands);
  TOKEN make7 = makeop(5); //ASSIGNOP
  TOKEN yes;

  asg->link = make2;

  if(sign == 1) {
    make3 = makeop(9); //LEOP
    make4 = makeop(1); //PLUSOP
  }
  else if(sign == -1) {
    make3 = makeop(10); //GEOP
    make4 = makeop(2); //MINUSOP
  }

  make6 = makeif(makeop(20), make3, make5, NULL);
  make6->operands = make3;
  make3->operands = copy;

  TOKEN copy2 = copytok(copy);
  if(sign == 1)
    yes = makeplus(copytok(copy2), makeintc(1), NULL);
  else if(sign == -1)
    yes = makeplus(copytok(copy2), makeintc(-1), NULL);
  make7->operands = copy2;
  copy2->link = yes;

  statement->link = make7;
  make7->link = makegoto(make2->operands->intval);
  make2->link = make6;
  copy->link = endexpr;
  return make;
}

TOKEN makeop(int opnum) {
  TOKEN tok;
  tok = (TOKEN) talloc();
  tok->tokentype = 0; //OPERATOR
  //tok->link = NULL;
  //tok->operands = NULL;
  tok->whichval = opnum;
  return tok;  
}

TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements) {
  TOKEN make = makeop(26); //PROGRAMOP
  TOKEN make2 = makepnb(talloc(), args);

  make->operands = name;
  make2->link = statements;
  name->link = make2;
  printf("\nfinished program\n");
  return make;
}

TOKEN makelabel() {
  TOKEN make = makeop(23); //LABELOP
  TOKEN make2 = makeintc(labelnumber++);
  make->operands = make2;
  return make;
}

TOKEN makeplus(TOKEN lhs, TOKEN rhs, TOKEN tok) {
  TOKEN yes = makeop(1); //PLUSOP
  if(rhs && lhs) {
    yes->operands = lhs;
    lhs->link = rhs;
    rhs->link = NULL;
  }
  return yes;
}

TOKEN copytok(TOKEN origtok) {
  TOKEN tok; int i;
  tok = (TOKEN) talloc();
  tok->tokentype = origtok->tokentype;
  tok->datatype  = origtok->datatype;
  tok->symtype   = origtok->symtype;
  tok->symentry  = origtok->symentry;
  //added more
  tok->operands = origtok->operands;
  tok->link = origtok->link;
  tok->whichval = origtok->whichval;
  tok->intval = origtok->intval;
  tok->realval = origtok->intval;

  for (i=0; i<16; i++) {
    tok->stringval[i] = origtok->stringval[i];
  }
  return tok;
}

//Helper
TOKEN changer_of_write(TOKEN go, TOKEN what) {
  TOKEN nope = NULL;
  int number1, number2;
  SYMBOL symba;

  if(what->datatype == 2) //STRINGTYPE
    return go;

  symba = searchst(go->stringval);
  number1 = symba->datatype->link->basicdt;
  number2 = what->datatype;

  if(number2 == 2) //STRINGTYPE
    nope = go;
  else {
    int comeback = 5;
    if(strcmp(go->stringval, "writeln") == 0)
      comeback = 7;
    if((strcmp(go->stringval, "write") == 0) || (strcmp(go->stringval, "writeln") == 0)) {
      if(number2 == 1) { //REAL
        go->stringval[comeback] = 'f';
        go->stringval[comeback+1] = '\0';
        nope = go; 
      }
      else if(number2 == 0) { //INTEGER
        go->stringval[comeback] = 'i';
        go->stringval[comeback+1] = '\0';
        nope = go;
      }
    }
  }
  return nope;
}


TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) {
  TOKEN yes;
  /*yes = makeop(5); //ASSIGNOP
  TOKEN make = makeop(24); //FUNCALLOP
  yes->operands = args;
  args->link = make;
  make->operands = fn;*/
  if(strcmp(fn->stringval, "new") != 0) {
    yes = makeop(24); //FUNCALLOP
    SYMBOL symba = searchst(fn->stringval);
    yes->datatype = symba->datatype->basicdt;
    if (strcmp(fn->stringval, "writeln") == 0 || strcmp(fn->stringval, "write") == 0) {
      fn = changer_of_write(fn, args);
      if (!fn) {
        printf("THIS IS THE PROBLEM\n\n\n");
        return NULL;
      }
    }
    yes->operands = fn;
    fn->link = args;
  }
  else {
    yes = makeop(5); //ASSIGNOP
    TOKEN nope = makeop(24); //FUNCALLOP
    SYMBOL symba2 = searchst(args->stringval);
    yes->operands = args;
    args->link = nope;
    nope->operands = fn;
    fn->link = makeintc(symba2->datatype->datatype->datatype->size);
  }
  return yes;
  
  /*yes->tokentype = 0; //OPERATOR
  yes->operands = fn;
  fn->link = args;
  return yes;*/
}

TOKEN makegoto(int label) {
  TOKEN make = makeop(21); //GOTOOP
  TOKEN make2 = makeintc(label);
  make->operands = make2;
  return make;  
}

TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
  { item->link = list;
    /*if (DEBUG & DB_CONS)
       { printf("cons\n");
         dbugprinttok(item);
         dbugprinttok(list);
       }*/
    return item;
  }

//Needed this as a helper function, could be done in binop
//but this is neater, cleaner, and much easier to read.
TOKEN binopHelp(TOKEN op, TOKEN lhs, TOKEN rhs) {
  int l = lhs->datatype;
  int r = rhs->datatype;
  int o = op->whichval;

  TOKEN yes;
  if (r == 1 && l == 0) {
    op->datatype = 1;
    if (o == 5) { //ASSIGNOP
      yes = makefix(rhs);
      op->operands = lhs;
      lhs->link = yes;
    }
    else {
      yes = makefloat(lhs);
      op->operands = yes;
      yes->link = rhs;
    }
  }
  else if (r == 0 && l == 1) {
    yes = makefloat(rhs);
    op->datatype = 1;
    op->operands = lhs;
    lhs->link = yes;
    yes->link = NULL;
    rhs->link = NULL;
  }
  else {
    op->datatype = lhs->datatype;
    op->operands = lhs;
    lhs->link = rhs;
    rhs->link = NULL;
  }
  return op;
}

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs)        /* reduce binary operator */
  { //op->operands = lhs;          /* link operands to operator       */
    //lhs->link = rhs;             /* link second operand to first    */
    //rhs->link = NULL;            /* terminate operand list          */
    int r, l, o;
    if(rhs->whichval == (302 - RESERVED_BIAS)) {
      rhs->tokentype = 5; //NUMBERTOK
      rhs->datatype = 0; //INTEGER
      rhs->whichval = 0;
    }
    r = rhs->datatype;
    l = lhs->datatype;

    if(l == r) {
      op->datatype = lhs->datatype;
      op->operands = lhs;
      lhs->link = rhs;
      rhs->link = NULL;
    }
    else
      op = binopHelp(op, lhs, rhs);

    /*if (DEBUG & DB_BINOP)
       { printf("binop\n");
         dbugprinttok(op);
         dbugprinttok(lhs);
         dbugprinttok(rhs);
       };*/
    return op;
  }

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart)
  {  tok->tokentype = OPERATOR;  /* Make it look like an operator   */
     tok->whichval = IFOP;
     if (elsepart != NULL) elsepart->link = NULL;
     thenpart->link = elsepart;
     exp->link = thenpart;
     tok->operands = exp;
     /*if (DEBUG & DB_MAKEIF)
        { printf("makeif\n");
          dbugprinttok(tok);
          dbugprinttok(exp);
          dbugprinttok(thenpart);
          dbugprinttok(elsepart);
        };*/
     return tok;
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

TOKEN makepnb(TOKEN tok, TOKEN statements) {
  if(1 && statements->whichval == 22) return statements; //PROGNOP
  return (makeprogn(tok, statements));
}

int wordaddress(int n, int wordsize)
  { return ((n + wordsize - 1) / wordsize) * wordsize; }

int yyerror(s)
  char * s;
  { 
    fputs(s,stderr); putc('\n',stderr);
    return 0;
  }

TOKEN findtype(TOKEN tok) {
  //int kind;
  SYMBOL p, sym;

  sym = searchst(tok->stringval);

  p = sym->datatype;
  //kind = sym->kind;

  if(sym->kind == 1) { //BASICTYPE
    tok->datatype = sym->basicdt;
    tok->symtype = sym;
  }
  else
    tok->symtype = p;
  return tok;
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


TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr) {
  TOKEN opo = makeop(22); //PROGNOP
  TOKEN ify = makeif(makeop(IFOP), expr, opo, NULL);
  TOKEN lab = makelabel();
  TOKEN pon = makepnb(talloc(), lab);
  TOKEN got = makegoto(lab->operands->intval);

  opo->link = got;
    lab->link = statements;
    lastyLastLink(statements)->link = ify;
  return pon;
}

TOKEN findid(TOKEN tok) {
  SYMBOL uno, dos;
  uno = searchst(tok->stringval);
  /*dos = searchst(tok->strival);*/
  if(uno->kind == 2) { //CONSTSYM
    tok->tokentype = 5; //NUMBERTOK
    if(uno->basicdt == 0) {
      tok->datatype = 0; //INTEGER
      tok->intval = uno->constval.intnum;
    }
    else if(uno->basicdt == 1) {
      tok->datatype = 1; //REAL
      tok->realval = uno->constval.realnum;
    }
  }
  else {
    tok->symentry = uno;
    dos = uno->datatype;
    tok->symtype = dos;
    if(dos->kind == 9 || dos->kind == 1) //POINTERSYM; BASICTYPE
      tok->datatype = dos->basicdt;
  }
  return tok;
}

void  instconst(TOKEN idtok, TOKEN consttok) {
  SYMBOL uno;

  uno = insertsym(idtok->stringval);
  uno->kind = 2; //CONSTSYM
  uno->basicdt = consttok->datatype;

  if(uno->basicdt == 2) { //STRINGTYPE
    strncpy(uno->constval.stringconst, consttok->stringval, 16);
    uno->size = basicsizes[2]; //STRINGTYPE
  }
  else if(uno->basicdt == 0) { //INTEGER
    uno->constval.intnum = consttok->intval;
    uno->size = basicsizes[0]; //INTEGER
  }
  else if(uno->basicdt == 1) { //REAL
    uno->constval.realnum = consttok->realval;
    uno->size = basicsizes[1]; //REAL
  }
  /*
  else
    return;
  */  
}

TOKEN maketimes(TOKEN lhs, TOKEN rhs, TOKEN tok) {
  TOKEN yes;
  yes = makeop(3); //TIMESOP
  if(rhs && lhs) {
    yes->operands = lhs;
    lhs->link - rhs;
    rhs->link = NULL;
  }
  return yes;
}

/*TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement) 
Do we need this, there's a while loop in the test code I think?

//last token thru the link
TOKEN get_last_link(TOKEN tok) {
  TOKEN un = tok;
  TOKEN next = un->link; //NEEDS MORE
  return un;
}

TOKEN get_last_operand(TOKEN tok) {
  
}

*/

TOKEN dopoint(TOKEN var, TOKEN tok) {
  tok->operands = var;
  return tok;
}

TOKEN makefix(TOKEN tok) {
  TOKEN yes; 
  yes = makeop(28); //FIXOP
  yes->operands = tok;
  yes->link = NULL;
  return yes;
}

TOKEN makefloat(TOKEN tok) {
  TOKEN yes;
  if(tok->tokentype == 5 && 1) { //NUMBERTOK
    yes = tok;
    yes->datatype = 1; //REAL
    yes->realval = yes->intval;
    yes->intval = INT_MIN; //this is minimum value of an integer. MACRO
  }
  else {
    yes = makeop(27); //FLOATOP
    yes->operands = tok;
    yes->link = NULL;
  }
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

TOKEN unaryop(TOKEN op, TOKEN lhs) {
  op->operands = lhs;
  lhs->link = NULL;
  return op;
}

//ADDED FOR PART 3

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

//helps get offset
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


TOKEN instdotdot(TOKEN lowtok, TOKEN dottok, TOKEN hightok) {
  return (makesubrange(dottok, lowtok->intval, hightok->intval));
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

TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement) {
  if (expr->operands->link->whichval == (302 - RESERVED_BIAS) && expr->operands->link) { //NIL
    expr->operands->link->tokentype = 5; //NUMBERTOK
    expr->operands->link->datatype = 0; //INTEGER
    expr->operands->link->whichval = 0;
  }

  TOKEN r = makepnb(talloc(), statement);
  TOKEN q = makelabel();
  TOKEN w = makegoto(q->operands->intval);
  TOKEN t = makeif(makeop(IFOP), expr, r, NULL);
  TOKEN e = makepnb(talloc(), q);

  q->link = t;

  if (r->whichval == 22) { // PROGNOP
    lastyLastLink(r->operands)->link = w;
  }
  else {
    r->operands = statement; 
    statement->link = w;
  }

  return e;
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

TOKEN addint(TOKEN exp, TOKEN off, TOKEN tok) {
  if(!off || !exp) {
    printf("THIS IS THE PROBLEM 3\n\n\n");
    return NULL;
  }
  int hi = exp->intval;
  int the = off->intval;

  exp->intval = the + hi;

  return exp;
}

//GIVING ME PROBLEMS!!!!!
void instlabel (TOKEN num) {
  arrForLabel[labelnumber++] == num->intval;
}

TOKEN dogoto(TOKEN tok, TOKEN labeltok) {
  int here;
  here = labelForMe(labeltok->intval);
  return (makegoto(here));
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

TOKEN makearef(TOKEN var, TOKEN off, TOKEN tok) {
  TOKEN yes;
  yes = makeop(25); //AREFOP
  yes->operands = var;
  var->link = off;
  return yes;
}

TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement) {
  int here;
  TOKEN make;
  TOKEN make2;
  TOKEN make3;
  TOKEN make4;
  here = labelForMe(labeltok->intval);
  make = makeop(22); //PROGNOP
  make2 = makeop(23); //LABELOP
  make3 = makeintc(here);

  make->operands = make2;
  make2->operands = make3;
  make2->link = statement;
  return make;
}

TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {
  TOKEN make;
  TOKEN yes;
  make = balance(var, field);

  if (var->whichval == 25) { //AREFOP
    if (make->whichval >= 0)
      var->operands->link = make;
    yes = var;
  }
  else
    yes = makearef(var, make, NULL);
  if (make->link && make->link->realval == -DBL_MAX && make->link->datatype == 1) { //REAL
    yes->datatype = 1; //REAL
    make->link = NULL;
  }
  return yes;
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

main()
  { int res;
    initsyms();
    res = yyparse();
    printst();
    printf("yyparse result = %8d\n", res);
    //if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
  }