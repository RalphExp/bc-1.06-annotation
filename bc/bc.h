/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

#ifndef YY_YY_Y_TAB_H_INCLUDED
# define YY_YY_Y_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    ENDOFLINE = 258,
    AND = 259,
    OR = 260,
    NOT = 261,
    STRING = 262,
    NAME = 263,
    NUMBER = 264,
    ASSIGN_OP = 265,
    REL_OP = 266,
    INCR_DECR = 267,
    Define = 268,
    Break = 269,
    Quit = 270,
    Length = 271,
    Return = 272,
    For = 273,
    If = 274,
    While = 275,
    Sqrt = 276,
    Else = 277,
    Scale = 278,
    Ibase = 279,
    Obase = 280,
    Auto = 281,
    Read = 282,
    Warranty = 283,
    Halt = 284,
    Last = 285,
    Continue = 286,
    Print = 287,
    Limits = 288,
    UNARY_MINUS = 289,
    HistoryVar = 290
  };
#endif
/* Tokens.  */
#define ENDOFLINE 258
#define AND 259
#define OR 260
#define NOT 261
#define STRING 262
#define NAME 263
#define NUMBER 264
#define ASSIGN_OP 265
#define REL_OP 266
#define INCR_DECR 267
#define Define 268
#define Break 269
#define Quit 270
#define Length 271
#define Return 272
#define For 273
#define If 274
#define While 275
#define Sqrt 276
#define Else 277
#define Scale 278
#define Ibase 279
#define Obase 280
#define Auto 281
#define Read 282
#define Warranty 283
#define Halt 284
#define Last 285
#define Continue 286
#define Print 287
#define Limits 288
#define UNARY_MINUS 289
#define HistoryVar 290

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED

union YYSTYPE
{
#line 40 "bc.y" /* yacc.c:1909  */

    char     *s_value;
    char      c_value;
    int       i_value;
    arg_list *a_value;

#line 131 "y.tab.h" /* yacc.c:1909  */
};

typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_Y_TAB_H_INCLUDED  */
