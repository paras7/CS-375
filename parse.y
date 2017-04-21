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

/* arrayref processes an array reference a[i]
   subs is a list of subscript expressions.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb) {


  TOKEN array_ref = NULL;
  SYMBOL arr_varsym, typesym, temp;
  SYMBOL arrsyms[10];

  arr_varsym = searchst(arr->stringval);


  temp = arr_varsym->datatype;

  int counter = 0;
  int num_arr_dims = 0; // not being used for anything

  while (temp && temp->kind != TYPESYM) {
    arrsyms[counter] = temp;
    num_arr_dims++;
    counter++;
    temp = temp->datatype;
  }

  typesym = temp;

  if (subs->link == NULL && subs->tokentype == NUMBERTOK) {
    int total_size = (subs->whichval - 1) * typesym->size;
    array_ref = makearef(arr, makeintc(total_size), NULL);
    array_ref->datatype = arr_varsym->basicdt;
    return array_ref;
  }
  // else if tokentype is IDENTIFIER?

  counter = 0;
  TOKEN curr_sub = subs;

  while (curr_sub) {

    if (counter == 0) {
      SYMBOL curr_sym = arrsyms[counter];
      int curr_size = curr_sym->size / (curr_sym->highbound - curr_sym->lowbound + 1);

      // TOKEN mul_op = maketimes(makeintc(curr_size), curr_sub, NULL);

      TOKEN mul_op = makeop(TIMESOP);
      TOKEN pos_typesym_size = makeintc(curr_size);
      TOKEN neg_typesym_size = makeintc(curr_size * -1);

      mul_op->operands = pos_typesym_size;
      pos_typesym_size->link = curr_sub;

      neg_typesym_size->link = mul_op;

      TOKEN plus_op = makeplus(neg_typesym_size, mul_op, NULL);

      array_ref = makearef(arr, plus_op, NULL);
      array_ref->datatype = arr_varsym->basicdt;

    }
    else {

      if (curr_sub->tokentype == NUMBERTOK) {   // only integers for now
        array_ref->operands->link->operands = addint(array_ref->operands->link->operands, 
          makeintc(curr_sub->whichval * typesym->size), NULL);
      }
      else {

        SYMBOL curr_sym = arrsyms[counter];
        int curr_size = curr_sym->size / (curr_sym->highbound - curr_sym->lowbound + 1);

        TOKEN mul_op = makeop(TIMESOP);
        TOKEN pos_typesym_size = makeintc(curr_size);
        TOKEN neg_typesym_size = makeintc(curr_size * -1);

        mul_op->operands = pos_typesym_size;
        pos_typesym_size->link = curr_sub;

        array_ref->operands->link->operands = addint(array_ref->operands->link->operands,
          neg_typesym_size, NULL);

        TOKEN add_to = array_ref->operands->link->operands->link;
        TOKEN plus_op = makeplus(add_to, mul_op, NULL);
        array_ref->operands->link->operands->link = plus_op;

      }
    }

    TOKEN unlink = curr_sub;
    curr_sub = curr_sub->link;
    unlink->link = NULL;
    counter++;
  }


  
  return array_ref;
}

/* dopoint handles a ^ operator.
   tok is a (now) unused token that is recycled. */
TOKEN dopoint(TOKEN var, TOKEN tok) {


  tok->operands = var;



  return tok;
}

/* instarray installs an array declaration into the symbol table.
   bounds points to a SUBRANGE symbol table entry.
   The symbol table pointer is returned in token typetok. */
TOKEN instarray(TOKEN bounds, TOKEN typetok) {


  // bounds->symtype->[low/highbound]

  TOKEN curr_bound = bounds;
  SYMBOL prev_sym = NULL;

  SYMBOL typesym = searchst(typetok->stringval);
  int low, high;

  while (curr_bound) {
    SYMBOL arrsym = symalloc();
    arrsym->kind = ARRAYSYM;

    if (typesym) {
      arrsym->datatype = typesym;
    }
    else {
//      arrsym->basicdt = typetok->datatype;
    }

    low = curr_bound->symtype->lowbound;
    high = curr_bound->symtype->highbound;

    if (!prev_sym) {
      arrsym->size = (high - low + 1) * typesym->size;
    }
    else {
      arrsym->datatype = typetok->symtype;
      arrsym->size = (high - low + 1) * prev_sym->size;
    }

    typetok->symtype = arrsym;
    prev_sym = arrsym;

    arrsym->lowbound = low;
    arrsym->highbound = high;

    curr_bound = curr_bound->link;
  }


  return typetok;
}

/* instdotdot installs a .. subrange in the symbol table.
   dottok is a (now) unused token that is recycled. */
TOKEN instdotdot(TOKEN lowtok, TOKEN dottok, TOKEN hightok) {


  TOKEN out = makesubrange(dottok, lowtok->intval, hightok->intval);



  return out;
}

/* instenum installs an enumerated subrange in the symbol table,
   e.g., type color = (red, white, blue)
   by calling makesubrange and returning the token it returns. */
TOKEN instenum(TOKEN idlist) {


  int total_size = 0;
  TOKEN temp = idlist;
  while (temp) {
    instconst(temp, makeintc(total_size));
    total_size++;
    temp = temp->link;
  }

  TOKEN subrange_tok = makesubrange(idlist, 0, (total_size - 1));



  return subrange_tok;
}

/* instfields will install type in a list idlist of field name tokens:
   re, im: real    put the pointer to REAL in the RE, IM tokens.
   typetok is a token whose symtype is a symbol table pointer.
   Note that nconc() can be used to combine these lists after instrec() */
TOKEN instfields(TOKEN idlist, TOKEN typetok) {


  int next = 0;
  int offset = 0;

  SYMBOL recsym, typesym;

  TOKEN temp = idlist;

  while (temp) {
    typesym = searchst(typetok->stringval);
    recsym = makesym(temp->stringval);
    recsym->datatype = typesym;

    // offset = next; next = next + n;
    offset = next;
    next = next + typesym->size;

    recsym->offset = offset;
    recsym->size = typesym->size;
    recsym->datatype = typesym;

    if (typesym->kind == BASICTYPE) {
      recsym->basicdt = typesym->basicdt;
    }

    temp->symtype = recsym;

    temp = temp->link;
  }



  return idlist;
}

/* instpoint will install a pointer type in symbol table */
TOKEN instpoint(TOKEN tok, TOKEN typename) {


  SYMBOL ptrsym, sym;

  ptrsym = symalloc();
  ptrsym->kind = POINTERSYM;
  ptrsym->basicdt = POINTER;
  ptrsym->size = basicsizes[POINTER];
  tok->symtype = ptrsym;

  sym = searchins(typename->stringval);
  sym->kind = TYPESYM;
  ptrsym->datatype = sym;


  tok->datatype = POINTER;

  return tok;
}

/* instrec will install a record definition.  Each token in the linked list
   argstok has a pointer its type.  rectok is just a trash token to be
   used to return the result in its symtype */
TOKEN instrec(TOKEN rectok, TOKEN argstok) {


  int total_size, offset;

  SYMBOL recsym = symalloc();
  recsym->kind = RECORDSYM;
  rectok->symtype = recsym;
  recsym->datatype = argstok->symtype;
  offset = wordaddress(argstok->symtype->size, 8);  // TODO: test this w/ something size 8
  total_size = offset;


  TOKEN curr = argstok;
  TOKEN next = argstok->link;
  while (next) {

    curr->symtype->link = next->symtype;
    offset = wordaddress(next->symtype->size, 8);   
    next->symtype->offset = total_size;
    total_size += offset;

    curr = next;
    next = next->link;
  }

  recsym->size = total_size;


  return rectok;
}

/* insttype will install a type name in symbol table.
   typetok is a token containing symbol table pointers. */
void insttype(TOKEN typename, TOKEN typetok) {


  SYMBOL sym, typesym;

  typesym = typetok->symtype;

  sym = searchins(typename->stringval);
  sym->kind = TYPESYM;
  sym->size = typesym->size;
  sym->datatype = typesym;
  sym->basicdt = typesym->basicdt;



}

/* makearef makes an array reference operation.
   off is be an integer constant token
   tok (if not NULL) is a (now) unused token that is recycled. */
TOKEN makearef(TOKEN var, TOKEN off, TOKEN tok) {
 

  TOKEN aref = makeop(AREFOP);
  aref->operands = var;
  var->link = off;

 
  
  return aref;
}

/* makesubrange makes a SUBRANGE symbol table entry, puts the pointer to it
   into tok, and returns tok. */
TOKEN makesubrange(TOKEN tok, int low, int high) {



  TOKEN out = copytok(tok);

  SYMBOL subrange_entry = symalloc();
  subrange_entry->kind = SUBRANGE;
  subrange_entry->basicdt = INTEGER;
  subrange_entry->lowbound = low;
  subrange_entry->highbound = high;
  subrange_entry->size = basicsizes[INTEGER];

  out->symtype = subrange_entry;


  return out;
}

/* nconc concatenates two token lists, destructively, by making the last link
   of lista point to listb.
   (nconc '(a b) '(c d e))  =  (a b c d e)  */
/* nconc is useful for putting together two fieldlist groups to
   make them into a single list in a record declaration. */
TOKEN nconc(TOKEN lista, TOKEN listb) {


  // TODO: check if lista contains members of listb or vice versa?

  get_last_link(lista)->link = listb;

 
  
  return lista;
}

TOKEN get_rec_field(TOKEN rec, TOKEN field) {

  TOKEN out = NULL;

  SYMBOL recsym = rec->symtype;
  while (recsym && !out) {
    if (strcmp(recsym->namestring, field->stringval) == 0) {
      out = talloc();
      out->symtype = recsym;
    }
    else {
      recsym = recsym->link;
    }
  }

  return out;
}

/* Gets and returns the last TOKEN (in)directly
   connected via ->operands to TOKEN tok. */
TOKEN get_last_operand(TOKEN tok) {
  if (!tok) {
    return NULL;
  }

  TOKEN curr = tok;
  TOKEN curr_operand = curr->operands;
  while (curr_operand) {
    curr = curr_operand;
    curr_operand = curr_operand->operands;
  }

  return curr;  
}

TOKEN makerealtok(float num) {
  TOKEN out = talloc();


  out->tokentype = NUMBERTOK;
  out->datatype = REAL;
  out->realval = num;

  return out;
}

TOKEN get_offset(TOKEN var, TOKEN field) {

  TOKEN offset = makeintc(-1);

  TOKEN root_name = get_last_operand(var);
  TOKEN last_offset = get_last_link(var->operands);

  SYMBOL found = NULL;
  SYMBOL varsym = searchst(root_name->stringval);

  bool var_is_arefop = 0;
  if (var->whichval == AREFOP) {
    var_is_arefop = 1;
  }
  


  SYMBOL temp = varsym;
  while (temp) {
    if (temp->datatype && temp->datatype->kind == BASICTYPE) {
      break;
    }
    temp = temp->datatype;
  }

 

  while (temp) {

    if ((strcmp(temp->namestring, field->stringval) == 0)) {
      found = temp;
      if (var_is_arefop) {

        if (last_offset->tokentype == OPERATOR) {
          offset->whichval = -1;
        }
        else {
          offset->whichval = last_offset->whichval + found->offset; 
        }

        if (found->datatype->basicdt == REAL) {
          offset->link = makerealtok(0);
          offset->link->realval = -DBL_MAX;
        }
      }
      else {

        offset->whichval = found->offset;
        if (found->datatype->basicdt == REAL) {
          offset->link = makerealtok(0);
          offset->link->realval = -DBL_MAX;
        }
      }

      return offset;
    }
    else if (var_is_arefop && (temp->offset == last_offset->whichval)) {
      found = temp;
      break;
    }

    temp = temp->link;
  }

  /* NOT an error condition if !found here. */

  if (!var_is_arefop && found) {
    offset->whichval = found->offset;
    if (found->datatype->basicdt == REAL) {
      offset->link = makerealtok(0);
      offset->link->realval = -DBL_MAX;
    }
    return offset;
  }
  else if (var_is_arefop && found) {

    SYMBOL temp1 = searchst(found->datatype->namestring);
    found = NULL;
 

    while (temp1) {
      if (temp1->datatype && temp1->datatype->kind == BASICTYPE) {
        break;
      }
      temp1 = temp1->datatype;
    }

  

    while (temp1 && !found) {
      if (strcmp(temp1->namestring, field->stringval) == 0) {
        found = temp1;
      }
      else {
        temp1 = temp1->link;
      }
    }

    /* NOT an error condition if !found here. */
    if (found) {
      offset->whichval = last_offset->whichval + found->offset;
      if (found->datatype->basicdt == REAL) {
        offset->link = makerealtok(0);
        offset->link->realval = -DBL_MAX;
      }

      return offset;
    }
  }

  return offset;
}

/* reducedot handles a record reference.
   dot is a (now) unused token that is recycled. */
TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {


  TOKEN aref;
  TOKEN offset = get_offset(var, field);

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

/* Gets and returns the last TOKEN (in)directly
   connected via ->link to TOKEN tok. Mostly used 
   to handle elimination of nested progns. */
TOKEN get_last_link(TOKEN tok) {
  if (!tok) {
    return NULL;
  }

  TOKEN curr = tok;
  TOKEN curr_link = curr->link;
  while (curr_link) {
    curr = curr_link;
    curr_link = curr_link->link;
  }

  return curr;
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
    get_last_link(do_progn_tok->operands)->link = stmt_incr_tok;
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
  get_last_link(statements)->link = ifop_tok;


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
    get_last_link(do_progn_tok->operands)->link = goto_tok;
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