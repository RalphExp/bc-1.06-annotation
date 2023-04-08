%{
/* bc.y: The grammar for a POSIX compatable bc processor with some
         extensions to the language. */

/*  This file is part of GNU bc.
    Copyright (C) 1991, 1992, 1993, 1994, 1997 Free Software Foundation, Inc.

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License , or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; see the file COPYING.  If not, write to:
      The Free Software Foundation, Inc.
      59 Temple Place, Suite 330
      Boston, MA 02111 USA

    You may contact the author by:
       e-mail:  philnelson@acm.org
      us-mail:  Philip A. Nelson
                Computer Science Department, 9062
                Western Washington University
                Bellingham, WA 98226-9062
       
*************************************************************************/

#include "bcdefs.h"
#include "global.h"
#include "proto.h"
%}

%start program

%union {
    char     *s_value;
    char      c_value;
    int            i_value;
    arg_list *a_value;
}

/* Extensions over POSIX bc.
   a) NAME was LETTER.  This grammar allows longer names.
      Single letter names will still work.
   b) Relational_expression allowed only one comparison.
      This grammar has added boolean expressions with
      && (and) || (or) and ! (not) and allowed all of them in
      full expressions.
   c) Added an else to the if.
   d) Call by variable array parameters
   e) read() procedure that reads a number under program control from stdin.
   f) halt statement that halts the the program under program control.  It
      is an executed statement.
   g) continue statement for for loops.
   h) optional expressions in the for loop.
   i) print statement to print multiple numbers per line.
   j) warranty statement to print an extended warranty notice.
   j) limits statement to print the processor's limits.
*/

%token <i_value> ENDOFLINE AND OR NOT
%token <s_value> STRING NAME NUMBER
/*     '-', '+' are tokens themselves        */
/*     '=', '+=',  '-=', '*=', '/=', '%=', '^=' */
%token <c_value> ASSIGN_OP
/*     '==', '<=', '>=', '!=', '<', '>'     */
%token <s_value> REL_OP
/*     '++', '--'                 */
%token <c_value> INCR_DECR
/*     'define', 'break', 'quit', 'length'     */
%token <i_value> Define    Break    Quit    Length
/*     'return', 'for', 'if', 'while', 'sqrt', 'else'     */
%token <i_value> Return    For    If    While    Sqrt   Else
/*     'scale', 'ibase', 'obase', 'auto', 'read'     */
%token <i_value> Scale    Ibase    Obase    Auto  Read
/*     'warranty', 'halt', 'last', 'continue', 'print', 'limits'   */
%token <i_value> Warranty, Halt, Last, Continue, Print, Limits
/*     'history' */
%token <i_value> UNARY_MINUS HistoryVar

/* Types of all other things. */
%type <i_value> expression return_expression named_expression opt_expression
%type <c_value> '+' '-' '*' '/' '%' 
%type <a_value> opt_parameter_list opt_auto_define_list define_list
%type <a_value> opt_argument_list argument_list
%type <i_value> program input_item semicolon_list statement_list
%type <i_value> statement function statement_or_error required_eol

/* precedence */
%left OR
%left AND
%nonassoc NOT
%left REL_OP
%right ASSIGN_OP
%left '+' '-'
%left '*' '/' '%'
%right '^'
%nonassoc UNARY_MINUS
%nonassoc INCR_DECR

%%
program            : /* empty */
                {
                  $$ = 0;
                  if (interactive && !quiet) {
                      show_bc_version ();
                      welcome ();
                  }
                }
            | program input_item
            ;
input_item        : semicolon_list ENDOFLINE
                { run_code (); }
            | function
                { run_code (); }
            | error ENDOFLINE
                {
                  yyerrok;
                  init_gen ();
                }
            ;
opt_newline        : /* empty */
            | ENDOFLINE
                { warn ("newline not allowed"); }
            ;
semicolon_list        : /* empty */
                { $$ = 0; }
            | statement_or_error
            | semicolon_list ';' statement_or_error
            | semicolon_list ';'
            ;
statement_list        : /* empty */
                { $$ = 0; }
            | statement_or_error
            | statement_list ENDOFLINE
            | statement_list ENDOFLINE statement_or_error
            | statement_list ';'
            | statement_list ';' statement
            ;
statement_or_error    : statement
              | error statement
                { $$ = $2; }
            ;
statement         : Warranty
                { warranty (""); }
            | Limits
                { limits (); }
            | expression
                {
                  if ($1 & 2)
                    warn ("comparison in expression");
                  if ($1 & 1)
                    generate ("W"); /* Write the value on the top of the stack.
                                       Then pop the stack. */
                  else
                    generate ("p"); /* Pop the execution stack. */
                }
            | STRING
                {
                  $$ = 0;
                  generate ("w");  /* Write a string to the output. TODO: write a newline */
                  generate ($1); /* ??? */
                  free ($1);
                }
            | Break
                {
                  if (break_label == 0)
                    yyerror ("Break outside a for/while");
                  else {
                      sprintf (genstr, "J%1d:", break_label); /* unconditional jump */
                      generate (genstr);
                  }
                }
            | Continue
                {
                  warn ("Continue statement");
                  if (continue_label == 0)
                    yyerror ("Continue outside a for");
                  else {
                      sprintf (genstr, "J%1d:", continue_label); /* unconditional jump */
                      generate (genstr);
                  }
                }
            | Quit
                { exit (0); }
            | Halt
                { generate ("h"); }
            | Return return_expression
                { generate ("R"); }
            | For
                {
                  $1 = break_label; /* save the old break label to $1, because the for block
                                      introduce a block scope. the old break label will be
                                      restored after the for block. */

                  break_label = next_label++; /* allocate a new break label used in the `for block`*/
                }
              '(' opt_expression ';'
                {
                  if ($4 & 2)
                    warn ("Comparison in first for expression");
                  if ($4 >= 0)
                    generate ("p");
                  $4 = next_label++;
                  sprintf (genstr, "N%1d:", $4); /* create a new label here,
                                                      before the second opt_expression */
                  generate (genstr);
                }
              opt_expression ';'
                {
                  if ($7 < 0) generate ("1"); /* if opt_expression is NULL, set TOS to 1. */
                  $7 = next_label++;
                  sprintf (genstr, "B%1d:J%1d:", $7, break_label); /* Test TOS if TOS != 0,
				                                        jump to $7(content of the for block),
                                                        otherwise jump to break_label, remove TOS. */
                  generate (genstr);
                  $<i_value>$ = continue_label; /* $<i_value>$ is the current block,
                                                  save the continue_label to $<i_value>$,
                                                  because for block introduce a block scope,
                                                  continue label will be restored after
                                                  the for block. */
                  continue_label = next_label++;
                  sprintf (genstr, "N%1d:", continue_label); /* a new continue label point to the
                                                               start of the third statement. */
                  generate (genstr);
                }
              opt_expression ')'
                {
                  if ($10 & 2 )
                    warn ("Comparison in third for expression");
                  if ($10 & 16)
                    sprintf (genstr, "J%1d:N%1d:", $4, $7); /* jump to $4, so the second expression
                                                            will be executed again in the for loop,
                                                            $7 is the label indicating the content of the
                                                            for statement, note that $7 is assigned in
                                                            the $9 block, (but generated here). */
                  else
                    sprintf (genstr, "pJ%1d:N%1d:", $4, $7);
                  generate (genstr);
                }
              opt_newline statement
                {
                  sprintf (genstr, "J%1d:N%1d:",  /* create a new label point to the end
                                                     of the for block.*/
                       continue_label, break_label);
                  generate (genstr);
                  break_label = $1;             /* end of for block, restore break label. */
                  continue_label = $<i_value>9; /* end of for block, restore continue label. */
                }
            | If '(' expression ')'
                {
                  $3 = if_label;                        /* save if label to $3*/
                  if_label = next_label++;              /* allocate a new label for the if block */
                  sprintf (genstr, "Z%1d:", if_label);  /* test the TOS, if TOS == 0, jump to the
				                                           end of the if block. */
                  generate (genstr);
                }
              opt_newline statement  opt_else
                {
                  sprintf (genstr, "N%1d:", if_label);  /* create the label point to the end of
				                                         if block. */
                  generate (genstr);
                  if_label = $3;                        /* restore if label */
                }
            | While
                {
                  $1 = next_label++;
                  sprintf (genstr, "N%1d:", $1);
                  generate (genstr);
                }
            '(' expression
                {
                  $4 = break_label;
                  break_label = next_label++;
                  sprintf (genstr, "Z%1d:", break_label);
                  generate (genstr);
                }
            ')' opt_newline statement
                {
                  sprintf (genstr, "J%1d:N%1d:", $1, break_label);
                  generate (genstr);
                  break_label = $4;
                }
            | '{' statement_list '}'
                { $$ = 0; }
            | Print
                {  warn ("print statement"); }
              print_list
            ;
print_list        : print_element
             | print_element ',' print_list
            ;
print_element        : STRING
                {
                  generate ("O");
                  generate ($1);
                  free ($1);
                }
            | expression
                { generate ("P"); }
             ;
opt_else        : /* nothing */
            | Else
                {
                  warn ("else clause in if statement");
                  $1 = next_label++;
                  sprintf (genstr, "J%d:N%1d:", $1, if_label);
                  generate (genstr);
                  if_label = $1;
                }
              opt_newline statement
function         : Define NAME '(' opt_parameter_list ')' opt_newline
                   '{' required_eol opt_auto_define_list
                {
                  /* Check auto list against parameter list? */
                  check_params ($4,$9);
                  sprintf (genstr, "F%d,%s.%s[",
                       lookup($2,FUNCTDEF), 
                       arg_str ($4), arg_str ($9));
                  generate (genstr);
                  free_args ($4);
                  free_args ($9);
                  $1 = next_label;
                  next_label = 1;
                }
              statement_list /* ENDOFLINE */ '}'
                {
                  generate ("0R]");
                  next_label = $1;
                }
            ;
opt_parameter_list    : /* empty */ 
                { $$ = NULL; }
            | define_list
            ;
opt_auto_define_list     : /* empty */ 
                { $$ = NULL; }
            | Auto define_list ENDOFLINE
                { $$ = $2; } 
            | Auto define_list ';'
                { $$ = $2; } 
            ;
define_list         : NAME
                { $$ = nextarg (NULL, lookup ($1,SIMPLE), FALSE);}
            | NAME '[' ']'
                { $$ = nextarg (NULL, lookup ($1,ARRAY), FALSE); }
            | '*' NAME '[' ']'
                { $$ = nextarg (NULL, lookup ($2,ARRAY), TRUE); }
            | define_list ',' NAME
                { $$ = nextarg ($1, lookup ($3,SIMPLE), FALSE); }
            | define_list ',' NAME '[' ']'
                { $$ = nextarg ($1, lookup ($3,ARRAY), FALSE); }
            | define_list ',' '*' NAME '[' ']'
                { $$ = nextarg ($1, lookup ($4,ARRAY), TRUE); }
            ;
opt_argument_list    : /* empty */
                { $$ = NULL; }
            | argument_list
            ;
argument_list         : expression
                {
                  if ($1 & 2) warn ("comparison in argument");
                  $$ = nextarg (NULL,0,FALSE);
                }
            | NAME '[' ']'
                {
                  sprintf (genstr, "K%d:", -lookup ($1,ARRAY));
                  generate (genstr);
                  $$ = nextarg (NULL,1,FALSE);
                }
            | argument_list ',' expression
                {
                  if ($3 & 2) warn ("comparison in argument");
                  $$ = nextarg ($1,0,FALSE);
                }
            | argument_list ',' NAME '[' ']'
                {
                  sprintf (genstr, "K%d:", -lookup ($3,ARRAY));
                  generate (genstr);
                  $$ = nextarg ($1,1,FALSE);
                }
            ;

/* Expression lval meanings!  (Bits mean something!)
 *  0 => Top op is assignment.
 *  1 => Top op is not assignment.
 *  2 => Comparison is somewhere in expression.
 *  4 => Expression is in parenthesis.
 * 16 => Empty optional expression.
 */

opt_expression         : /* empty */
                {
                  $$ = 16;
                  warn ("Missing expression in for statement");
                }
            | expression
            ;
return_expression    : /* empty */
                {
                  $$ = 0;
                  generate ("0");
                }
            | expression
                {
                  if ($1 & 2)
                    warn ("comparison in return expresion");
                  if (!($1 & 4))
                    warn ("return expression requires parenthesis");
                }
            ;
expression        :  named_expression ASSIGN_OP 
                {
                  if ($2 != '=')
                {
                  if ($1 < 0)
                    sprintf (genstr, "DL%d:", -$1);
                  else
                    sprintf (genstr, "l%d:", $1);
                  generate (genstr);
                }
                }
              expression
                {
                  if ($4 & 2) warn("comparison in assignment");
                  if ($2 != '=')
                {
                  sprintf (genstr, "%c", $2);
                  generate (genstr);
                }
                  if ($1 < 0)
                sprintf (genstr, "S%d:", -$1);
                  else
                sprintf (genstr, "s%d:", $1);
                  generate (genstr);
                  $$ = 0;
                }
            ;
            | expression AND 
                {
                  warn("&& operator");
                  $2 = next_label++;
                  sprintf (genstr, "DZ%d:p", $2);
                  generate (genstr);
                }
              expression
                {
                  sprintf (genstr, "DZ%d:p1N%d:", $2, $2);
                  generate (genstr);
                  $$ = ($1 | $4) & ~4;
                }
            | expression OR
                {
                  warn("|| operator");
                  $2 = next_label++;
                  sprintf (genstr, "B%d:", $2);
                  generate (genstr);
                }
              expression
                 {
                  int tmplab;
                  tmplab = next_label++;
                  sprintf (genstr, "B%d:0J%d:N%d:1N%d:",
                       $2, tmplab, $2, tmplab);
                  generate (genstr);
                  $$ = ($1 | $4) & ~4;
                }
            | NOT expression
                {
                  $$ = $2 & ~4;
                  warn("! operator");
                  generate ("!");
                }
            | expression REL_OP expression
                {
                  $$ = 3;
                  switch (*($2))
                {
                case '=':
                  generate ("=");
                  break;

                case '!':
                  generate ("#");
                  break;

                case '<':
                  if ($2[1] == '=')
                    generate ("{");
                  else
                    generate ("<");
                  break;

                case '>':
                  if ($2[1] == '=')
                    generate ("}");
                  else
                    generate (">");
                  break;
                }
                }
            | expression '+' expression
                {
                  generate ("+");
                  $$ = ($1 | $3) & ~4;
                }
            | expression '-' expression
                {
                  generate ("-");
                  $$ = ($1 | $3) & ~4;
                }
            | expression '*' expression
                {
                  generate ("*");
                  $$ = ($1 | $3) & ~4;
                }
            | expression '/' expression
                {
                  generate ("/");
                  $$ = ($1 | $3) & ~4;
                }
            | expression '%' expression
                {
                  generate ("%");
                  $$ = ($1 | $3) & ~4;
                }
            | expression '^' expression
                {
                  generate ("^");
                  $$ = ($1 | $3) & ~4;
                }
            | '-' expression  %prec UNARY_MINUS
                {
                  generate ("n");
                  $$ = $2 & ~4;
                }
            | named_expression
                {
                  $$ = 1;
                  if ($1 < 0)
                sprintf (genstr, "L%d:", -$1);
                  else
                sprintf (genstr, "l%d:", $1);
                  generate (genstr);
                }
            | NUMBER
                {
                  int len = strlen($1);
                  $$ = 1;
                  if (len == 1 && *$1 == '0')
                generate ("0");
                  else if (len == 1 && *$1 == '1')
                generate ("1");
                  else
                {
                  generate ("K");
                  generate ($1);
                  generate (":");
                }
                  free ($1);
                }
            | '(' expression ')'
                { $$ = $2 | 5; }
            | NAME '(' opt_argument_list ')'
                {
                  $$ = 1;
                  if ($3 != NULL)
                { 
                  sprintf (genstr, "C%d,%s:",
                       lookup ($1,FUNCT),
                       call_str ($3));
                  free_args ($3);
                }
                  else
                {
                  sprintf (genstr, "C%d:", lookup ($1,FUNCT));
                }
                  generate (genstr);
                }
            | INCR_DECR named_expression
                {
                  $$ = 1;
                  if ($2 < 0)
                {
                  if ($1 == '+')
                    sprintf (genstr, "DA%d:L%d:", -$2, -$2);
                  else
                    sprintf (genstr, "DM%d:L%d:", -$2, -$2);
                }
                  else
                {
                  if ($1 == '+')
                    sprintf (genstr, "i%d:l%d:", $2, $2);
                  else
                    sprintf (genstr, "d%d:l%d:", $2, $2);
                }
                  generate (genstr);
                }
            | named_expression INCR_DECR
                {
                  $$ = 1;
                  if ($1 < 0)
                {
                  sprintf (genstr, "DL%d:x", -$1);
                  generate (genstr); 
                  if ($2 == '+')
                    sprintf (genstr, "A%d:", -$1);
                  else
                      sprintf (genstr, "M%d:", -$1);
                }
                  else
                {
                  sprintf (genstr, "l%d:", $1);
                  generate (genstr);
                  if ($2 == '+')
                    sprintf (genstr, "i%d:", $1);
                  else
                    sprintf (genstr, "d%d:", $1);
                }
                  generate (genstr);
                }
            | Length '(' expression ')'
                { generate ("cL"); $$ = 1;}
            | Sqrt '(' expression ')'
                { generate ("cR"); $$ = 1;}
            | Scale '(' expression ')'
                { generate ("cS"); $$ = 1;}
            | Read '(' ')'
                {
                  warn ("read function");
                  generate ("cI"); $$ = 1;
                }
            ;
named_expression    : NAME
                { $$ = lookup($1,SIMPLE); }
            | NAME '[' expression ']'
                {
                  if ($3 > 1) warn("comparison in subscript");
                  $$ = lookup($1,ARRAY);
                }
            | Ibase
                { $$ = 0; }
            | Obase
                { $$ = 1; }
            | Scale
                { $$ = 2; }
            | HistoryVar
                { $$ = 3;
                  warn ("History variable");
                }
            | Last
                { $$ = 4;
                  warn ("Last variable");
                }
            ;


required_eol        : { warn ("End of line required"); }
            | ENDOFLINE
            | required_eol ENDOFLINE
              { warn ("Too many end of lines"); }
            ;

%%

