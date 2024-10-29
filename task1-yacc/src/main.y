%{
    #include <assert.h>
    #include <ctype.h>
    #include <stdio.h>
    #include <math.h>
    int yylex(void);
    void yyerror(const char *);
%}

%union {
    double value;
}

%token <value> NUM
%type <value> exp

%%

input:
    {}
|   input line
;

line:
    '\n'
|   exp '\n'        { printf ("%.10g\n", $1); }
;

exp:
    NUM             { $$ = $1; }
|   exp exp '+'     { $$ = $1 + $2; }
|   exp exp '-'     { $$ = $1 - $2; }
|   exp exp '*'     { $$ = $1 * $2; }
|   exp exp '/'     { $$ = $1 / $2; }
|   exp exp '^'     { $$ = pow($1, $2); }
|   exp 'n'         { $$ = -$1; }
;

%%

int yylex(void) {
    int c;

    while (isblank(c = getchar ()))
        continue;

    if (c == '.' || isdigit(c)) {
        ungetc(c, stdin);
        int ret = scanf("%lf", &yylval.value);
        assert(ret != 0);
        return NUM;
    }

    if (c == EOF || c == '!')
        return 0;

    return c;
}

int main(int argc, char **argv) {
    return yyparse();
}

void yyerror(const char *s) {
    fprintf(stderr, "%s\n", s);
}
