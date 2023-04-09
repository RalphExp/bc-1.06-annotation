/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison implementation for Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.4"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* Copy the first part of user declarations.  */
#line 1 "bc.y" /* yacc.c:339  */

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

#line 103 "y.tab.c" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* In a future release of Bison, this section will be replaced
   by #include "y.tab.h".  */
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
#line 40 "bc.y" /* yacc.c:355  */

    char     *s_value;
    char      c_value;
    int       i_value;
    arg_list *a_value;

#line 220 "y.tab.c" /* yacc.c:355  */
};

typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_Y_TAB_H_INCLUDED  */

/* Copy the second part of user declarations.  */

#line 237 "y.tab.c" /* yacc.c:358  */

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  2
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   693

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  50
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  35
/* YYNRULES -- Number of rules.  */
#define YYNRULES  107
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  185

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   290

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,    40,     2,     2,
      43,    44,    38,    36,    47,    37,     2,    39,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,    42,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    48,     2,    49,    41,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    45,     2,    46,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   108,   108,   115,   117,   119,   121,   127,   128,   132,
     133,   134,   135,   138,   139,   140,   141,   142,   143,   145,
     146,   149,   151,   153,   163,   170,   179,   189,   191,   193,
     196,   204,   215,   233,   195,   256,   255,   271,   277,   270,
     293,   296,   295,   299,   300,   302,   308,   311,   313,   312,
     323,   321,   342,   343,   346,   347,   349,   352,   354,   356,
     358,   360,   362,   366,   367,   369,   374,   380,   385,   402,
     406,   409,   413,   422,   421,   449,   448,   462,   461,   477,
     483,   511,   516,   521,   526,   531,   536,   541,   546,   555,
     571,   573,   589,   608,   631,   633,   635,   637,   643,   645,
     650,   652,   654,   656,   660,   667,   668,   669
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 0
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "ENDOFLINE", "AND", "OR", "NOT",
  "STRING", "NAME", "NUMBER", "ASSIGN_OP", "REL_OP", "INCR_DECR", "Define",
  "Break", "Quit", "Length", "Return", "For", "If", "While", "Sqrt",
  "Else", "Scale", "Ibase", "Obase", "Auto", "Read", "Warranty", "Halt",
  "Last", "Continue", "Print", "Limits", "UNARY_MINUS", "HistoryVar",
  "'+'", "'-'", "'*'", "'/'", "'%'", "'^'", "';'", "'('", "')'", "'{'",
  "'}'", "','", "'['", "']'", "$accept", "program", "input_item",
  "opt_newline", "semicolon_list", "statement_list", "statement_or_error",
  "statement", "$@1", "$@2", "@3", "$@4", "$@5", "$@6", "$@7", "$@8",
  "print_list", "print_element", "opt_else", "$@9", "function", "$@10",
  "opt_parameter_list", "opt_auto_define_list", "define_list",
  "opt_argument_list", "argument_list", "opt_expression",
  "return_expression", "expression", "$@11", "$@12", "$@13",
  "named_expression", "required_eol", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,    43,    45,    42,    47,
      37,    94,    59,    40,    41,   123,   125,    44,    91,    93
};
# endif

#define YYPACT_NINF -134

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-134)))

#define YYTABLE_NINF -16

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
    -134,   170,  -134,   375,   567,  -134,   -41,  -134,    66,     9,
    -134,  -134,   -35,   567,  -134,   -32,  -134,   -29,   -25,  -134,
    -134,   -19,  -134,  -134,  -134,  -134,  -134,  -134,  -134,   567,
     567,   213,  -134,     3,  -134,  -134,  -134,   642,    27,  -134,
    -134,    -6,   597,   567,   -21,  -134,  -134,    30,   567,  -134,
     642,    38,   567,    40,   567,   567,    15,   537,  -134,   122,
     505,     6,  -134,  -134,   305,  -134,  -134,   567,   567,   567,
     567,   567,   567,   567,  -134,  -134,   -28,    18,    13,   642,
      39,     2,   410,   567,   419,   567,   428,   466,  -134,  -134,
    -134,    46,   642,  -134,   259,   505,  -134,  -134,   567,   567,
     404,    64,    64,    44,    44,    44,    44,   567,   107,  -134,
     627,  -134,    47,    78,    43,    52,  -134,    58,   642,  -134,
     642,  -134,  -134,   537,  -134,  -134,    -6,   652,   404,  -134,
     -22,   642,    59,    62,   108,    17,  -134,   108,    68,  -134,
     337,  -134,    65,  -134,    72,    70,   112,   567,   505,   108,
    -134,  -134,   118,    75,    77,    87,   113,   505,  -134,    10,
    -134,    89,  -134,  -134,  -134,  -134,  -134,     2,  -134,  -134,
     567,   108,    16,   213,    92,   505,  -134,  -134,    19,  -134,
    -134,  -134,   108,   505,  -134
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       2,     0,     1,     0,     0,    24,    98,    89,     0,     0,
      25,    27,     0,    71,    30,     0,    37,     0,   102,   100,
     101,     0,    21,    28,   104,    26,    41,    22,   103,     0,
       0,     0,     3,     0,    10,    19,     5,    23,    88,     6,
      20,    79,    63,     0,    98,   102,    92,     0,     0,    29,
      72,     0,     0,     0,     0,     0,     0,     0,    87,     0,
       0,     0,    14,     4,     0,    75,    77,     0,     0,     0,
       0,     0,     0,     0,    73,    93,    98,     0,    64,    65,
       0,    52,     0,    69,     0,     0,     0,     0,    97,    45,
      42,    43,    46,    90,     0,    17,    40,    11,     0,     0,
      80,    81,    82,    83,    84,    85,    86,     0,     0,    91,
       0,    99,    57,     0,     0,    53,    94,     0,    70,    35,
      38,    95,    96,     0,    16,    18,    76,    78,    74,    66,
      98,    67,     0,     0,     7,     0,    31,     7,     0,    44,
       0,    58,     0,     8,     0,    60,     0,    69,     0,     7,
      68,    59,   105,     0,     0,     0,    47,     0,   106,    54,
      61,     0,    32,    48,    36,    39,   107,     0,    50,    62,
      69,     7,     0,     0,     0,     0,    55,    56,     0,    33,
      49,    51,     7,     0,    34
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -134,  -134,  -134,  -133,  -134,   -33,     0,    -3,  -134,  -134,
    -134,  -134,  -134,  -134,  -134,  -134,    20,  -134,  -134,  -134,
    -134,  -134,  -134,  -134,   -26,  -134,  -134,  -124,  -134,    -1,
    -134,  -134,  -134,   139,  -134
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     1,    32,   144,    33,    61,    62,    35,    51,   147,
     170,   182,   137,    53,   138,    57,    90,    91,   164,   171,
      36,   173,   114,   168,   115,    77,    78,   117,    49,    37,
     107,    98,    99,    38,   159
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      40,    34,    42,    41,   148,    67,    63,    43,    48,    94,
     112,    52,    50,   166,    54,    42,   157,    47,    55,   176,
     108,    42,    94,   155,    56,   145,   140,    43,    58,    59,
      68,    69,    70,    71,    72,    73,   167,    74,   175,    75,
     113,    79,    80,    65,    66,    64,   174,    82,    95,   183,
      67,    84,    96,    86,    87,   146,    92,    40,   177,    88,
     110,    95,   109,   135,    97,   181,   100,   101,   102,   103,
     104,   105,   106,    81,    44,    68,    69,    70,    71,    72,
      73,    83,   118,    85,   120,    73,   133,   134,   111,    45,
      19,    20,   125,   123,   124,   132,    24,   126,   127,   135,
     136,    28,    70,    71,    72,    73,   128,    80,   141,   131,
     142,   143,   149,     4,   151,     6,     7,   152,   153,     8,
     154,   158,    92,    12,   160,   161,    65,    66,    17,   162,
      18,    19,    20,    67,    21,   163,   179,    24,   169,    80,
     178,   172,    28,   139,    29,   156,   118,    46,     0,     0,
      30,     0,     0,     0,   165,     0,   129,     0,    68,    69,
      70,    71,    72,    73,     0,     0,    93,     0,     0,   118,
       2,     3,   180,    -9,     0,     0,     4,     5,     6,     7,
     184,     0,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    17,     0,    18,    19,    20,     0,    21,    22,    23,
      24,    25,    26,    27,     0,    28,     0,    29,     0,     0,
       0,     0,    -9,    30,    60,    31,   -13,     0,     0,     4,
       5,     6,     7,     0,     0,     8,     0,    10,    11,    12,
      13,    14,    15,    16,    17,     0,    18,    19,    20,     0,
      21,    22,    23,    24,    25,    26,    27,     0,    28,     0,
      29,     0,     0,     0,     0,   -13,    30,     0,    31,   -13,
      60,     0,   -15,     0,     0,     4,     5,     6,     7,     0,
       0,     8,     0,    10,    11,    12,    13,    14,    15,    16,
      17,     0,    18,    19,    20,     0,    21,    22,    23,    24,
      25,    26,    27,     0,    28,     0,    29,     0,     0,     0,
       0,   -15,    30,     0,    31,   -15,    60,     0,   -12,     0,
       0,     4,     5,     6,     7,     0,     0,     8,     0,    10,
      11,    12,    13,    14,    15,    16,    17,     0,    18,    19,
      20,     0,    21,    22,    23,    24,    25,    26,    27,     0,
      28,     0,    29,     4,     0,     6,     7,   -12,    30,     8,
      31,     0,     0,    12,     0,     0,     0,     0,    17,     0,
      18,    19,    20,     0,    21,     0,     0,    24,     0,     0,
       0,     0,    28,     0,    29,     0,     0,     0,    39,     0,
      30,     4,     5,     6,     7,     0,   150,     8,     0,    10,
      11,    12,    13,    14,    15,    16,    17,     0,    18,    19,
      20,     0,    21,    22,    23,    24,    25,    26,    27,     0,
      28,     0,    29,     0,    65,    66,     0,     0,    30,     0,
      31,    67,     0,    65,    66,     0,     0,     0,     0,     0,
      67,     0,    65,    66,     0,     0,     0,     0,     0,    67,
      68,    69,    70,    71,    72,    73,    68,    69,    70,    71,
      72,    73,     0,     0,   116,    68,    69,    70,    71,    72,
      73,     0,     0,   119,    68,    69,    70,    71,    72,    73,
      65,    66,   121,     0,     0,     0,     0,    67,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    68,    69,    70,    71,    72,    73,     0,     0,
     122,     4,     5,     6,     7,     0,     0,     8,     0,    10,
      11,    12,    13,    14,    15,    16,    17,     0,    18,    19,
      20,     0,    21,    22,    23,    24,    25,    26,    27,     0,
      28,     0,    29,     4,    89,     6,     7,     0,    30,     8,
      31,     0,     0,    12,     0,     0,     0,     0,    17,     0,
      18,    19,    20,     0,    21,     0,     0,    24,     0,     0,
       0,     0,    28,     4,    29,     6,     7,     0,     0,     8,
      30,     0,     0,    12,     0,     0,     0,     0,    17,     0,
      18,    19,    20,     0,    21,     0,     0,    24,     0,     0,
       0,     0,    28,     4,    29,    76,     7,     0,     0,     8,
      30,     0,     0,    12,     0,     0,     0,     0,    17,     0,
      18,    19,    20,     0,    21,     0,     0,    24,     0,     0,
       0,     0,    28,     4,    29,   130,     7,     0,     0,     8,
      30,     0,     0,    12,     0,     0,    65,    66,    17,     0,
      18,    19,    20,    67,    21,     0,    65,    24,     0,     0,
       0,     0,    28,    67,    29,     0,     0,     0,     0,     0,
      30,     0,     0,     0,     0,     0,     0,     0,    68,    69,
      70,    71,    72,    73,     0,     0,     0,     0,    68,    69,
      70,    71,    72,    73
};

static const yytype_int16 yycheck[] =
{
       3,     1,    43,     4,   137,    11,     3,    48,    43,     3,
       8,    43,    13,     3,    43,    43,   149,     8,    43,     3,
      48,    43,     3,   147,    43,     8,    48,    48,    29,    30,
      36,    37,    38,    39,    40,    41,    26,    10,   171,    12,
      38,    42,    43,     4,     5,    42,   170,    48,    42,   182,
      11,    52,    46,    54,    55,    38,    57,    60,    42,    44,
      47,    42,    44,    47,    64,    46,    67,    68,    69,    70,
      71,    72,    73,    43,     8,    36,    37,    38,    39,    40,
      41,    43,    83,    43,    85,    41,     8,    44,    49,    23,
      24,    25,    95,    47,    94,    48,    30,    98,    99,    47,
      42,    35,    38,    39,    40,    41,   107,   108,    49,   110,
      48,     3,    44,     6,    49,     8,     9,    45,    48,    12,
       8,     3,   123,    16,    49,    48,     4,     5,    21,    42,
      23,    24,    25,    11,    27,    22,    44,    30,    49,   140,
     173,   167,    35,   123,    37,   148,   147,     8,    -1,    -1,
      43,    -1,    -1,    -1,   157,    -1,    49,    -1,    36,    37,
      38,    39,    40,    41,    -1,    -1,    44,    -1,    -1,   170,
       0,     1,   175,     3,    -1,    -1,     6,     7,     8,     9,
     183,    -1,    12,    13,    14,    15,    16,    17,    18,    19,
      20,    21,    -1,    23,    24,    25,    -1,    27,    28,    29,
      30,    31,    32,    33,    -1,    35,    -1,    37,    -1,    -1,
      -1,    -1,    42,    43,     1,    45,     3,    -1,    -1,     6,
       7,     8,     9,    -1,    -1,    12,    -1,    14,    15,    16,
      17,    18,    19,    20,    21,    -1,    23,    24,    25,    -1,
      27,    28,    29,    30,    31,    32,    33,    -1,    35,    -1,
      37,    -1,    -1,    -1,    -1,    42,    43,    -1,    45,    46,
       1,    -1,     3,    -1,    -1,     6,     7,     8,     9,    -1,
      -1,    12,    -1,    14,    15,    16,    17,    18,    19,    20,
      21,    -1,    23,    24,    25,    -1,    27,    28,    29,    30,
      31,    32,    33,    -1,    35,    -1,    37,    -1,    -1,    -1,
      -1,    42,    43,    -1,    45,    46,     1,    -1,     3,    -1,
      -1,     6,     7,     8,     9,    -1,    -1,    12,    -1,    14,
      15,    16,    17,    18,    19,    20,    21,    -1,    23,    24,
      25,    -1,    27,    28,    29,    30,    31,    32,    33,    -1,
      35,    -1,    37,     6,    -1,     8,     9,    42,    43,    12,
      45,    -1,    -1,    16,    -1,    -1,    -1,    -1,    21,    -1,
      23,    24,    25,    -1,    27,    -1,    -1,    30,    -1,    -1,
      -1,    -1,    35,    -1,    37,    -1,    -1,    -1,     3,    -1,
      43,     6,     7,     8,     9,    -1,    49,    12,    -1,    14,
      15,    16,    17,    18,    19,    20,    21,    -1,    23,    24,
      25,    -1,    27,    28,    29,    30,    31,    32,    33,    -1,
      35,    -1,    37,    -1,     4,     5,    -1,    -1,    43,    -1,
      45,    11,    -1,     4,     5,    -1,    -1,    -1,    -1,    -1,
      11,    -1,     4,     5,    -1,    -1,    -1,    -1,    -1,    11,
      36,    37,    38,    39,    40,    41,    36,    37,    38,    39,
      40,    41,    -1,    -1,    44,    36,    37,    38,    39,    40,
      41,    -1,    -1,    44,    36,    37,    38,    39,    40,    41,
       4,     5,    44,    -1,    -1,    -1,    -1,    11,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    36,    37,    38,    39,    40,    41,    -1,    -1,
      44,     6,     7,     8,     9,    -1,    -1,    12,    -1,    14,
      15,    16,    17,    18,    19,    20,    21,    -1,    23,    24,
      25,    -1,    27,    28,    29,    30,    31,    32,    33,    -1,
      35,    -1,    37,     6,     7,     8,     9,    -1,    43,    12,
      45,    -1,    -1,    16,    -1,    -1,    -1,    -1,    21,    -1,
      23,    24,    25,    -1,    27,    -1,    -1,    30,    -1,    -1,
      -1,    -1,    35,     6,    37,     8,     9,    -1,    -1,    12,
      43,    -1,    -1,    16,    -1,    -1,    -1,    -1,    21,    -1,
      23,    24,    25,    -1,    27,    -1,    -1,    30,    -1,    -1,
      -1,    -1,    35,     6,    37,     8,     9,    -1,    -1,    12,
      43,    -1,    -1,    16,    -1,    -1,    -1,    -1,    21,    -1,
      23,    24,    25,    -1,    27,    -1,    -1,    30,    -1,    -1,
      -1,    -1,    35,     6,    37,     8,     9,    -1,    -1,    12,
      43,    -1,    -1,    16,    -1,    -1,     4,     5,    21,    -1,
      23,    24,    25,    11,    27,    -1,     4,    30,    -1,    -1,
      -1,    -1,    35,    11,    37,    -1,    -1,    -1,    -1,    -1,
      43,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    36,    37,
      38,    39,    40,    41,    -1,    -1,    -1,    -1,    36,    37,
      38,    39,    40,    41
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    51,     0,     1,     6,     7,     8,     9,    12,    13,
      14,    15,    16,    17,    18,    19,    20,    21,    23,    24,
      25,    27,    28,    29,    30,    31,    32,    33,    35,    37,
      43,    45,    52,    54,    56,    57,    70,    79,    83,     3,
      57,    79,    43,    48,     8,    23,    83,     8,    43,    78,
      79,    58,    43,    63,    43,    43,    43,    65,    79,    79,
       1,    55,    56,     3,    42,     4,     5,    11,    36,    37,
      38,    39,    40,    41,    10,    12,     8,    75,    76,    79,
      79,    43,    79,    43,    79,    43,    79,    79,    44,     7,
      66,    67,    79,    44,     3,    42,    46,    56,    81,    82,
      79,    79,    79,    79,    79,    79,    79,    80,    48,    44,
      47,    49,     8,    38,    72,    74,    44,    77,    79,    44,
      79,    44,    44,    47,    56,    57,    79,    79,    79,    49,
       8,    79,    48,     8,    44,    47,    42,    62,    64,    66,
      48,    49,    48,     3,    53,     8,    38,    59,    53,    44,
      49,    49,    45,    48,     8,    77,    57,    53,     3,    84,
      49,    48,    42,    22,    68,    57,     3,    26,    73,    49,
      60,    69,    74,    71,    77,    53,     3,    42,    55,    44,
      57,    46,    61,    53,    57
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    50,    51,    51,    52,    52,    52,    53,    53,    54,
      54,    54,    54,    55,    55,    55,    55,    55,    55,    56,
      56,    57,    57,    57,    57,    57,    57,    57,    57,    57,
      58,    59,    60,    61,    57,    62,    57,    63,    64,    57,
      57,    65,    57,    66,    66,    67,    67,    68,    69,    68,
      71,    70,    72,    72,    73,    73,    73,    74,    74,    74,
      74,    74,    74,    75,    75,    76,    76,    76,    76,    77,
      77,    78,    78,    80,    79,    81,    79,    82,    79,    79,
      79,    79,    79,    79,    79,    79,    79,    79,    79,    79,
      79,    79,    79,    79,    79,    79,    79,    79,    83,    83,
      83,    83,    83,    83,    83,    84,    84,    84
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     0,     2,     2,     1,     2,     0,     1,     0,
       1,     3,     2,     0,     1,     2,     3,     2,     3,     1,
       2,     1,     1,     1,     1,     1,     1,     1,     1,     2,
       0,     0,     0,     0,    14,     0,     8,     0,     0,     8,
       3,     0,     3,     1,     3,     1,     1,     0,     0,     4,
       0,    12,     0,     1,     0,     3,     3,     1,     3,     4,
       3,     5,     6,     0,     1,     1,     3,     3,     5,     0,
       1,     0,     1,     0,     4,     0,     4,     0,     4,     2,
       3,     3,     3,     3,     3,     3,     3,     2,     1,     1,
       3,     4,     2,     2,     4,     4,     4,     3,     1,     4,
       1,     1,     1,     1,     1,     0,     1,     2
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, int yyrule)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                                              );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
yystrlen (const char *yystr)
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
{
  YYUSE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        YYSTYPE *yyvs1 = yyvs;
        yytype_int16 *yyss1 = yyss;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yystacksize);

        yyss = yyss1;
        yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yytype_int16 *yyss1 = yyss;
        union yyalloc *yyptr =
          (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
                  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 108 "bc.y" /* yacc.c:1646  */
    {
                  (yyval.i_value) = 0;
                  if (interactive && !quiet) {
                      show_bc_version ();
                      welcome ();
                  }
                }
#line 1556 "y.tab.c" /* yacc.c:1646  */
    break;

  case 4:
#line 118 "bc.y" /* yacc.c:1646  */
    { run_code (); }
#line 1562 "y.tab.c" /* yacc.c:1646  */
    break;

  case 5:
#line 120 "bc.y" /* yacc.c:1646  */
    { run_code (); }
#line 1568 "y.tab.c" /* yacc.c:1646  */
    break;

  case 6:
#line 122 "bc.y" /* yacc.c:1646  */
    {
                  yyerrok;
                  init_gen ();
                }
#line 1577 "y.tab.c" /* yacc.c:1646  */
    break;

  case 8:
#line 129 "bc.y" /* yacc.c:1646  */
    { warn ("newline not allowed"); }
#line 1583 "y.tab.c" /* yacc.c:1646  */
    break;

  case 9:
#line 132 "bc.y" /* yacc.c:1646  */
    { (yyval.i_value) = 0; }
#line 1589 "y.tab.c" /* yacc.c:1646  */
    break;

  case 13:
#line 138 "bc.y" /* yacc.c:1646  */
    { (yyval.i_value) = 0; }
#line 1595 "y.tab.c" /* yacc.c:1646  */
    break;

  case 20:
#line 147 "bc.y" /* yacc.c:1646  */
    { (yyval.i_value) = (yyvsp[0].i_value); }
#line 1601 "y.tab.c" /* yacc.c:1646  */
    break;

  case 21:
#line 150 "bc.y" /* yacc.c:1646  */
    { warranty (""); }
#line 1607 "y.tab.c" /* yacc.c:1646  */
    break;

  case 22:
#line 152 "bc.y" /* yacc.c:1646  */
    { limits (); }
#line 1613 "y.tab.c" /* yacc.c:1646  */
    break;

  case 23:
#line 154 "bc.y" /* yacc.c:1646  */
    {
                  if ((yyvsp[0].i_value) & 2)
                    warn ("comparison in expression");
                  if ((yyvsp[0].i_value) & 1)
                    generate ("W"); /* Write the value on the top of the stack.
                                       Then pop the stack. */
                  else
                    generate ("p"); /* Pop the execution stack. */
                }
#line 1627 "y.tab.c" /* yacc.c:1646  */
    break;

  case 24:
#line 164 "bc.y" /* yacc.c:1646  */
    {
                  (yyval.i_value) = 0;
                  generate ("w");  /* Write a string to the output. TODO: write a newline */
                  generate ((yyvsp[0].s_value)); /* ??? */
                  free ((yyvsp[0].s_value));
                }
#line 1638 "y.tab.c" /* yacc.c:1646  */
    break;

  case 25:
#line 171 "bc.y" /* yacc.c:1646  */
    {
                  if (break_label == 0)
                    yyerror ("Break outside a for/while");
                  else {
                      sprintf (genstr, "J%1d:", break_label); /* unconditional jump */
                      generate (genstr);
                  }
                }
#line 1651 "y.tab.c" /* yacc.c:1646  */
    break;

  case 26:
#line 180 "bc.y" /* yacc.c:1646  */
    {
                  warn ("Continue statement");
                  if (continue_label == 0)
                    yyerror ("Continue outside a for");
                  else {
                      sprintf (genstr, "J%1d:", continue_label); /* unconditional jump */
                      generate (genstr);
                  }
                }
#line 1665 "y.tab.c" /* yacc.c:1646  */
    break;

  case 27:
#line 190 "bc.y" /* yacc.c:1646  */
    { exit (0); }
#line 1671 "y.tab.c" /* yacc.c:1646  */
    break;

  case 28:
#line 192 "bc.y" /* yacc.c:1646  */
    { generate ("h"); }
#line 1677 "y.tab.c" /* yacc.c:1646  */
    break;

  case 29:
#line 194 "bc.y" /* yacc.c:1646  */
    { generate ("R"); }
#line 1683 "y.tab.c" /* yacc.c:1646  */
    break;

  case 30:
#line 196 "bc.y" /* yacc.c:1646  */
    {
                  (yyvsp[0].i_value) = break_label; /* save the old break label to $1, because the for block
                                      introduce a block scope. the old break label will be
                                      restored after the for block. */

                  break_label = next_label++; /* allocate a new break label used in the `for block`*/
                }
#line 1695 "y.tab.c" /* yacc.c:1646  */
    break;

  case 31:
#line 204 "bc.y" /* yacc.c:1646  */
    {
                  if ((yyvsp[-1].i_value) & 2)
                    warn ("Comparison in first for expression");
                  if ((yyvsp[-1].i_value) >= 0)
                    generate ("p");
                  (yyvsp[-1].i_value) = next_label++;
                  sprintf (genstr, "N%1d:", (yyvsp[-1].i_value)); /* create a new label here,
                                                    before the second opt_expression */
                  generate (genstr);
                }
#line 1710 "y.tab.c" /* yacc.c:1646  */
    break;

  case 32:
#line 215 "bc.y" /* yacc.c:1646  */
    {
                  if ((yyvsp[-1].i_value) < 0) generate ("1"); /* if opt_expression is NULL, set TOS to 1. */
                  (yyvsp[-1].i_value) = next_label++;
                  sprintf (genstr, "B%1d:J%1d:", (yyvsp[-1].i_value), break_label); /* Test TOS if TOS != 0,
				                                        jump to $7(content of the for block),
                                                otherwise jump to break_label, remove TOS. */
                  generate (genstr);
                  (yyval.i_value) = continue_label; /* $<i_value>$ is the current block,
                                                  save the continue_label to $<i_value>$,
                                                  because for block introduce a block scope,
                                                  continue label will be restored after
                                                  the for block. */
                  continue_label = next_label++;
                  sprintf (genstr, "N%1d:", continue_label); /* a new continue label point to the
                                                               start of the third statement. */
                  generate (genstr);
                }
#line 1732 "y.tab.c" /* yacc.c:1646  */
    break;

  case 33:
#line 233 "bc.y" /* yacc.c:1646  */
    {
                  if ((yyvsp[-1].i_value) & 2 )
                    warn ("Comparison in third for expression");
                  if ((yyvsp[-1].i_value) & 16)
                    sprintf (genstr, "J%1d:N%1d:", (yyvsp[-7].i_value), (yyvsp[-4].i_value)); /* jump to $4, so the second expression
                                                            will be executed again in the for loop,
                                                            $7 is the label indicating the content of the
                                                            for statement, note that $7 is assigned in
                                                            the $9 block, (but generated here). */
                  else
                    sprintf (genstr, "pJ%1d:N%1d:", (yyvsp[-7].i_value), (yyvsp[-4].i_value));
                  generate (genstr);
                }
#line 1750 "y.tab.c" /* yacc.c:1646  */
    break;

  case 34:
#line 247 "bc.y" /* yacc.c:1646  */
    {
                  sprintf (genstr, "J%1d:N%1d:",  /* create a new label point to the end
                                                     of the for block.*/
                       continue_label, break_label);
                  generate (genstr);
                  break_label = (yyvsp[-13].i_value);             /* end of for block, restore break label. */
                  continue_label = (yyvsp[-5].i_value); /* end of for block, restore continue label. */
                }
#line 1763 "y.tab.c" /* yacc.c:1646  */
    break;

  case 35:
#line 256 "bc.y" /* yacc.c:1646  */
    {
                  (yyvsp[-1].i_value) = if_label;                        /* save if label to $3*/
                  if_label = next_label++;              /* allocate a new label for the if block */
                  sprintf (genstr, "Z%1d:", if_label);  /* test the TOS, if TOS == 0, jump to the
				                                                   end of the if block. */
                  generate (genstr);
                }
#line 1775 "y.tab.c" /* yacc.c:1646  */
    break;

  case 36:
#line 264 "bc.y" /* yacc.c:1646  */
    {
                  sprintf (genstr, "N%1d:", if_label);  /* create the label point to the end of
				                                                   if block. */
                  generate (genstr);
                  if_label = (yyvsp[-5].i_value);                        /* restore if label */
                }
#line 1786 "y.tab.c" /* yacc.c:1646  */
    break;

  case 37:
#line 271 "bc.y" /* yacc.c:1646  */
    {
                  (yyvsp[0].i_value) = next_label++;
                  sprintf (genstr, "N%1d:", (yyvsp[0].i_value));        /* create a new label for the while block. */
                  generate (genstr);
                }
#line 1796 "y.tab.c" /* yacc.c:1646  */
    break;

  case 38:
#line 277 "bc.y" /* yacc.c:1646  */
    {
                  (yyvsp[0].i_value) = break_label;                        /* save the old break label, which will be restored
                                                              after the while block. */
                  break_label = next_label++;              /* allocate a new break label. */
                  sprintf (genstr, "Z%1d:", break_label);  /* check TOS, jump to the the end of the while block
                                                              if TOS == 0 */
                  generate (genstr);
                }
#line 1809 "y.tab.c" /* yacc.c:1646  */
    break;

  case 39:
#line 286 "bc.y" /* yacc.c:1646  */
    {
                  sprintf (genstr, "J%1d:N%1d:", (yyvsp[-7].i_value), break_label); /* JUMP to the beginning of the while block,
                                                                      also create a new label for the end of 
                                                                      while block. */
                  generate (genstr);
                  break_label = (yyvsp[-4].i_value);
                }
#line 1821 "y.tab.c" /* yacc.c:1646  */
    break;

  case 40:
#line 294 "bc.y" /* yacc.c:1646  */
    { (yyval.i_value) = 0; }
#line 1827 "y.tab.c" /* yacc.c:1646  */
    break;

  case 41:
#line 296 "bc.y" /* yacc.c:1646  */
    {  warn ("print statement"); }
#line 1833 "y.tab.c" /* yacc.c:1646  */
    break;

  case 45:
#line 303 "bc.y" /* yacc.c:1646  */
    {
                  generate ("O");
                  generate ((yyvsp[0].s_value));
                  free ((yyvsp[0].s_value));
                }
#line 1843 "y.tab.c" /* yacc.c:1646  */
    break;

  case 46:
#line 309 "bc.y" /* yacc.c:1646  */
    { generate ("P"); }
#line 1849 "y.tab.c" /* yacc.c:1646  */
    break;

  case 48:
#line 313 "bc.y" /* yacc.c:1646  */
    {
                  warn ("else clause in if statement");
                  (yyvsp[0].i_value) = next_label++;
                  sprintf (genstr, "J%d:N%1d:", (yyvsp[0].i_value), if_label);
                  generate (genstr);
                  if_label = (yyvsp[0].i_value);
                }
#line 1861 "y.tab.c" /* yacc.c:1646  */
    break;

  case 50:
#line 323 "bc.y" /* yacc.c:1646  */
    {
                  /* Check auto list against parameter list? */
                  check_params ((yyvsp[-5].a_value),(yyvsp[0].a_value));
                  sprintf (genstr, "F%d,%s.%s[",
                       lookup((yyvsp[-7].s_value),FUNCTDEF), 
                       arg_str ((yyvsp[-5].a_value)), arg_str ((yyvsp[0].a_value)));
                  generate (genstr);
                  free_args ((yyvsp[-5].a_value));
                  free_args ((yyvsp[0].a_value));
                  (yyvsp[-8].i_value) = next_label;
                  next_label = 1;
                }
#line 1878 "y.tab.c" /* yacc.c:1646  */
    break;

  case 51:
#line 336 "bc.y" /* yacc.c:1646  */
    {
                  generate ("0R]");
                  next_label = (yyvsp[-11].i_value);
                }
#line 1887 "y.tab.c" /* yacc.c:1646  */
    break;

  case 52:
#line 342 "bc.y" /* yacc.c:1646  */
    { (yyval.a_value) = NULL; }
#line 1893 "y.tab.c" /* yacc.c:1646  */
    break;

  case 54:
#line 346 "bc.y" /* yacc.c:1646  */
    { (yyval.a_value) = NULL; }
#line 1899 "y.tab.c" /* yacc.c:1646  */
    break;

  case 55:
#line 348 "bc.y" /* yacc.c:1646  */
    { (yyval.a_value) = (yyvsp[-1].a_value); }
#line 1905 "y.tab.c" /* yacc.c:1646  */
    break;

  case 56:
#line 350 "bc.y" /* yacc.c:1646  */
    { (yyval.a_value) = (yyvsp[-1].a_value); }
#line 1911 "y.tab.c" /* yacc.c:1646  */
    break;

  case 57:
#line 353 "bc.y" /* yacc.c:1646  */
    { (yyval.a_value) = nextarg (NULL, lookup ((yyvsp[0].s_value),SIMPLE), FALSE);}
#line 1917 "y.tab.c" /* yacc.c:1646  */
    break;

  case 58:
#line 355 "bc.y" /* yacc.c:1646  */
    { (yyval.a_value) = nextarg (NULL, lookup ((yyvsp[-2].s_value),ARRAY), FALSE); }
#line 1923 "y.tab.c" /* yacc.c:1646  */
    break;

  case 59:
#line 357 "bc.y" /* yacc.c:1646  */
    { (yyval.a_value) = nextarg (NULL, lookup ((yyvsp[-2].s_value),ARRAY), TRUE); }
#line 1929 "y.tab.c" /* yacc.c:1646  */
    break;

  case 60:
#line 359 "bc.y" /* yacc.c:1646  */
    { (yyval.a_value) = nextarg ((yyvsp[-2].a_value), lookup ((yyvsp[0].s_value),SIMPLE), FALSE); }
#line 1935 "y.tab.c" /* yacc.c:1646  */
    break;

  case 61:
#line 361 "bc.y" /* yacc.c:1646  */
    { (yyval.a_value) = nextarg ((yyvsp[-4].a_value), lookup ((yyvsp[-2].s_value),ARRAY), FALSE); }
#line 1941 "y.tab.c" /* yacc.c:1646  */
    break;

  case 62:
#line 363 "bc.y" /* yacc.c:1646  */
    { (yyval.a_value) = nextarg ((yyvsp[-5].a_value), lookup ((yyvsp[-2].s_value),ARRAY), TRUE); }
#line 1947 "y.tab.c" /* yacc.c:1646  */
    break;

  case 63:
#line 366 "bc.y" /* yacc.c:1646  */
    { (yyval.a_value) = NULL; }
#line 1953 "y.tab.c" /* yacc.c:1646  */
    break;

  case 65:
#line 370 "bc.y" /* yacc.c:1646  */
    {
                  if ((yyvsp[0].i_value) & 2) warn ("comparison in argument");
                  (yyval.a_value) = nextarg (NULL,0,FALSE);
                }
#line 1962 "y.tab.c" /* yacc.c:1646  */
    break;

  case 66:
#line 375 "bc.y" /* yacc.c:1646  */
    {
                  sprintf (genstr, "K%d:", -lookup ((yyvsp[-2].s_value),ARRAY));
                  generate (genstr);
                  (yyval.a_value) = nextarg (NULL,1,FALSE);
                }
#line 1972 "y.tab.c" /* yacc.c:1646  */
    break;

  case 67:
#line 381 "bc.y" /* yacc.c:1646  */
    {
                  if ((yyvsp[0].i_value) & 2) warn ("comparison in argument");
                  (yyval.a_value) = nextarg ((yyvsp[-2].a_value),0,FALSE);
                }
#line 1981 "y.tab.c" /* yacc.c:1646  */
    break;

  case 68:
#line 386 "bc.y" /* yacc.c:1646  */
    {
                  sprintf (genstr, "K%d:", -lookup ((yyvsp[-2].s_value),ARRAY));
                  generate (genstr);
                  (yyval.a_value) = nextarg ((yyvsp[-4].a_value),1,FALSE);
                }
#line 1991 "y.tab.c" /* yacc.c:1646  */
    break;

  case 69:
#line 402 "bc.y" /* yacc.c:1646  */
    {
                  (yyval.i_value) = 16;
                  warn ("Missing expression in for statement");
                }
#line 2000 "y.tab.c" /* yacc.c:1646  */
    break;

  case 71:
#line 409 "bc.y" /* yacc.c:1646  */
    {
                  (yyval.i_value) = 0;
                  generate ("0");
                }
#line 2009 "y.tab.c" /* yacc.c:1646  */
    break;

  case 72:
#line 414 "bc.y" /* yacc.c:1646  */
    {
                  if ((yyvsp[0].i_value) & 2)
                    warn ("comparison in return expresion");
                  if (!((yyvsp[0].i_value) & 4))
                    warn ("return expression requires parenthesis");
                }
#line 2020 "y.tab.c" /* yacc.c:1646  */
    break;

  case 73:
#line 422 "bc.y" /* yacc.c:1646  */
    {
                  if ((yyvsp[0].c_value) != '=')
                {
                  if ((yyvsp[-1].i_value) < 0)
                    sprintf (genstr, "DL%d:", -(yyvsp[-1].i_value));
                  else
                    sprintf (genstr, "l%d:", (yyvsp[-1].i_value));
                  generate (genstr);
                }
                }
#line 2035 "y.tab.c" /* yacc.c:1646  */
    break;

  case 74:
#line 433 "bc.y" /* yacc.c:1646  */
    {
                  if ((yyvsp[0].i_value) & 2) warn("comparison in assignment");
                  if ((yyvsp[-2].c_value) != '=')
                {
                  sprintf (genstr, "%c", (yyvsp[-2].c_value));
                  generate (genstr);
                }
                  if ((yyvsp[-3].i_value) < 0)
                sprintf (genstr, "S%d:", -(yyvsp[-3].i_value));
                  else
                sprintf (genstr, "s%d:", (yyvsp[-3].i_value));
                  generate (genstr);
                  (yyval.i_value) = 0;
                }
#line 2054 "y.tab.c" /* yacc.c:1646  */
    break;

  case 75:
#line 449 "bc.y" /* yacc.c:1646  */
    {
                  warn("&& operator");
                  (yyvsp[0].i_value) = next_label++;
                  sprintf (genstr, "DZ%d:p", (yyvsp[0].i_value));
                  generate (genstr);
                }
#line 2065 "y.tab.c" /* yacc.c:1646  */
    break;

  case 76:
#line 456 "bc.y" /* yacc.c:1646  */
    {
                  sprintf (genstr, "DZ%d:p1N%d:", (yyvsp[-2].i_value), (yyvsp[-2].i_value));
                  generate (genstr);
                  (yyval.i_value) = ((yyvsp[-3].i_value) | (yyvsp[0].i_value)) & ~4;
                }
#line 2075 "y.tab.c" /* yacc.c:1646  */
    break;

  case 77:
#line 462 "bc.y" /* yacc.c:1646  */
    {
                  warn("|| operator");
                  (yyvsp[0].i_value) = next_label++;
                  sprintf (genstr, "B%d:", (yyvsp[0].i_value));
                  generate (genstr);
                }
#line 2086 "y.tab.c" /* yacc.c:1646  */
    break;

  case 78:
#line 469 "bc.y" /* yacc.c:1646  */
    {
                  int tmplab;
                  tmplab = next_label++;
                  sprintf (genstr, "B%d:0J%d:N%d:1N%d:",
                       (yyvsp[-2].i_value), tmplab, (yyvsp[-2].i_value), tmplab);
                  generate (genstr);
                  (yyval.i_value) = ((yyvsp[-3].i_value) | (yyvsp[0].i_value)) & ~4;
                }
#line 2099 "y.tab.c" /* yacc.c:1646  */
    break;

  case 79:
#line 478 "bc.y" /* yacc.c:1646  */
    {
                  (yyval.i_value) = (yyvsp[0].i_value) & ~4;
                  warn("! operator");
                  generate ("!");
                }
#line 2109 "y.tab.c" /* yacc.c:1646  */
    break;

  case 80:
#line 484 "bc.y" /* yacc.c:1646  */
    {
                  (yyval.i_value) = 3;
                  switch (*((yyvsp[-1].s_value)))
                {
                case '=':
                  generate ("=");
                  break;

                case '!':
                  generate ("#");
                  break;

                case '<':
                  if ((yyvsp[-1].s_value)[1] == '=')
                    generate ("{");
                  else
                    generate ("<");
                  break;

                case '>':
                  if ((yyvsp[-1].s_value)[1] == '=')
                    generate ("}");
                  else
                    generate (">");
                  break;
                }
                }
#line 2141 "y.tab.c" /* yacc.c:1646  */
    break;

  case 81:
#line 512 "bc.y" /* yacc.c:1646  */
    {
                  generate ("+");
                  (yyval.i_value) = ((yyvsp[-2].i_value) | (yyvsp[0].i_value)) & ~4;
                }
#line 2150 "y.tab.c" /* yacc.c:1646  */
    break;

  case 82:
#line 517 "bc.y" /* yacc.c:1646  */
    {
                  generate ("-");
                  (yyval.i_value) = ((yyvsp[-2].i_value) | (yyvsp[0].i_value)) & ~4;
                }
#line 2159 "y.tab.c" /* yacc.c:1646  */
    break;

  case 83:
#line 522 "bc.y" /* yacc.c:1646  */
    {
                  generate ("*");
                  (yyval.i_value) = ((yyvsp[-2].i_value) | (yyvsp[0].i_value)) & ~4;
                }
#line 2168 "y.tab.c" /* yacc.c:1646  */
    break;

  case 84:
#line 527 "bc.y" /* yacc.c:1646  */
    {
                  generate ("/");
                  (yyval.i_value) = ((yyvsp[-2].i_value) | (yyvsp[0].i_value)) & ~4;
                }
#line 2177 "y.tab.c" /* yacc.c:1646  */
    break;

  case 85:
#line 532 "bc.y" /* yacc.c:1646  */
    {
                  generate ("%");
                  (yyval.i_value) = ((yyvsp[-2].i_value) | (yyvsp[0].i_value)) & ~4;
                }
#line 2186 "y.tab.c" /* yacc.c:1646  */
    break;

  case 86:
#line 537 "bc.y" /* yacc.c:1646  */
    {
                  generate ("^");
                  (yyval.i_value) = ((yyvsp[-2].i_value) | (yyvsp[0].i_value)) & ~4;
                }
#line 2195 "y.tab.c" /* yacc.c:1646  */
    break;

  case 87:
#line 542 "bc.y" /* yacc.c:1646  */
    {
                  generate ("n");
                  (yyval.i_value) = (yyvsp[0].i_value) & ~4;
                }
#line 2204 "y.tab.c" /* yacc.c:1646  */
    break;

  case 88:
#line 547 "bc.y" /* yacc.c:1646  */
    {
                  (yyval.i_value) = 1;
                  if ((yyvsp[0].i_value) < 0)
                sprintf (genstr, "L%d:", -(yyvsp[0].i_value));
                  else
                sprintf (genstr, "l%d:", (yyvsp[0].i_value));
                  generate (genstr);
                }
#line 2217 "y.tab.c" /* yacc.c:1646  */
    break;

  case 89:
#line 556 "bc.y" /* yacc.c:1646  */
    {
                  int len = strlen((yyvsp[0].s_value));
                  (yyval.i_value) = 1;
                  if (len == 1 && *(yyvsp[0].s_value) == '0')
                generate ("0");
                  else if (len == 1 && *(yyvsp[0].s_value) == '1')
                generate ("1");
                  else
                {
                  generate ("K");
                  generate ((yyvsp[0].s_value));
                  generate (":");
                }
                  free ((yyvsp[0].s_value));
                }
#line 2237 "y.tab.c" /* yacc.c:1646  */
    break;

  case 90:
#line 572 "bc.y" /* yacc.c:1646  */
    { (yyval.i_value) = (yyvsp[-1].i_value) | 5; }
#line 2243 "y.tab.c" /* yacc.c:1646  */
    break;

  case 91:
#line 574 "bc.y" /* yacc.c:1646  */
    {
                  (yyval.i_value) = 1;
                  if ((yyvsp[-1].a_value) != NULL)
                { 
                  sprintf (genstr, "C%d,%s:",
                       lookup ((yyvsp[-3].s_value),FUNCT),
                       call_str ((yyvsp[-1].a_value)));
                  free_args ((yyvsp[-1].a_value));
                }
                  else
                {
                  sprintf (genstr, "C%d:", lookup ((yyvsp[-3].s_value),FUNCT));
                }
                  generate (genstr);
                }
#line 2263 "y.tab.c" /* yacc.c:1646  */
    break;

  case 92:
#line 590 "bc.y" /* yacc.c:1646  */
    {
                  (yyval.i_value) = 1;
                  if ((yyvsp[0].i_value) < 0)
                {
                  if ((yyvsp[-1].c_value) == '+')
                    sprintf (genstr, "DA%d:L%d:", -(yyvsp[0].i_value), -(yyvsp[0].i_value));
                  else
                    sprintf (genstr, "DM%d:L%d:", -(yyvsp[0].i_value), -(yyvsp[0].i_value));
                }
                  else
                {
                  if ((yyvsp[-1].c_value) == '+')
                    sprintf (genstr, "i%d:l%d:", (yyvsp[0].i_value), (yyvsp[0].i_value));
                  else
                    sprintf (genstr, "d%d:l%d:", (yyvsp[0].i_value), (yyvsp[0].i_value));
                }
                  generate (genstr);
                }
#line 2286 "y.tab.c" /* yacc.c:1646  */
    break;

  case 93:
#line 609 "bc.y" /* yacc.c:1646  */
    {
                  (yyval.i_value) = 1;
                  if ((yyvsp[-1].i_value) < 0)
                {
                  sprintf (genstr, "DL%d:x", -(yyvsp[-1].i_value));
                  generate (genstr); 
                  if ((yyvsp[0].c_value) == '+')
                    sprintf (genstr, "A%d:", -(yyvsp[-1].i_value));
                  else
                      sprintf (genstr, "M%d:", -(yyvsp[-1].i_value));
                }
                  else
                {
                  sprintf (genstr, "l%d:", (yyvsp[-1].i_value));
                  generate (genstr);
                  if ((yyvsp[0].c_value) == '+')
                    sprintf (genstr, "i%d:", (yyvsp[-1].i_value));
                  else
                    sprintf (genstr, "d%d:", (yyvsp[-1].i_value));
                }
                  generate (genstr);
                }
#line 2313 "y.tab.c" /* yacc.c:1646  */
    break;

  case 94:
#line 632 "bc.y" /* yacc.c:1646  */
    { generate ("cL"); (yyval.i_value) = 1;}
#line 2319 "y.tab.c" /* yacc.c:1646  */
    break;

  case 95:
#line 634 "bc.y" /* yacc.c:1646  */
    { generate ("cR"); (yyval.i_value) = 1;}
#line 2325 "y.tab.c" /* yacc.c:1646  */
    break;

  case 96:
#line 636 "bc.y" /* yacc.c:1646  */
    { generate ("cS"); (yyval.i_value) = 1;}
#line 2331 "y.tab.c" /* yacc.c:1646  */
    break;

  case 97:
#line 638 "bc.y" /* yacc.c:1646  */
    {
                  warn ("read function");
                  generate ("cI"); (yyval.i_value) = 1;
                }
#line 2340 "y.tab.c" /* yacc.c:1646  */
    break;

  case 98:
#line 644 "bc.y" /* yacc.c:1646  */
    { (yyval.i_value) = lookup((yyvsp[0].s_value),SIMPLE); }
#line 2346 "y.tab.c" /* yacc.c:1646  */
    break;

  case 99:
#line 646 "bc.y" /* yacc.c:1646  */
    {
                  if ((yyvsp[-1].i_value) > 1) warn("comparison in subscript");
                  (yyval.i_value) = lookup((yyvsp[-3].s_value),ARRAY);
                }
#line 2355 "y.tab.c" /* yacc.c:1646  */
    break;

  case 100:
#line 651 "bc.y" /* yacc.c:1646  */
    { (yyval.i_value) = 0; }
#line 2361 "y.tab.c" /* yacc.c:1646  */
    break;

  case 101:
#line 653 "bc.y" /* yacc.c:1646  */
    { (yyval.i_value) = 1; }
#line 2367 "y.tab.c" /* yacc.c:1646  */
    break;

  case 102:
#line 655 "bc.y" /* yacc.c:1646  */
    { (yyval.i_value) = 2; }
#line 2373 "y.tab.c" /* yacc.c:1646  */
    break;

  case 103:
#line 657 "bc.y" /* yacc.c:1646  */
    { (yyval.i_value) = 3;
                  warn ("History variable");
                }
#line 2381 "y.tab.c" /* yacc.c:1646  */
    break;

  case 104:
#line 661 "bc.y" /* yacc.c:1646  */
    { (yyval.i_value) = 4;
                  warn ("Last variable");
                }
#line 2389 "y.tab.c" /* yacc.c:1646  */
    break;

  case 105:
#line 667 "bc.y" /* yacc.c:1646  */
    { warn ("End of line required"); }
#line 2395 "y.tab.c" /* yacc.c:1646  */
    break;

  case 107:
#line 670 "bc.y" /* yacc.c:1646  */
    { warn ("Too many end of lines"); }
#line 2401 "y.tab.c" /* yacc.c:1646  */
    break;


#line 2405 "y.tab.c" /* yacc.c:1646  */
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
#line 673 "bc.y" /* yacc.c:1906  */


