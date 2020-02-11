/* -*- Mode: Java -*- */

%code imports {
import java.io.Reader;
import java.util.List;
import java.util.LinkedList;

@SuppressWarnings({"unchecked", "fallthrough", "unused"})
}

%language "Java"

%locations

%define package "de.dfki.lt.loot.tfs.io"

%define public

%define parser_class_name "RestrictorParser"

%code {
/* A grammar for restrictor FSs in jxchg format with type generalizations
 */

}

%token < String >  ID
%token < String >  NUMBER

%type < FS > fs
%type < List > typeGen typeGens
%type < FeatVal > featVals
%type < Variable > var

%%

fs : '[' ID typeGen featVals ']' { $$ = new FS($2, $3, $4); }
   ;

typeGen : '{' typeGens '}' { $$ = $2.reverse(); }
        | { $$ = null; }
        ;

typeGens : ID ',' typeGens { $1.add($3); $$ = $1; }
         | ID { $$ = new LinkedList().add($1); }
         ;

featVals : ID fs { $$ = new FeatVal($1, $2); }
         | ID var { $$ = new FeatVal($1, $2); }
         | ID var fs {  $$ = new FeatVal($1, new Conjunction($2, $3)); }
         ;

var : '#' NUMBER { new Variable($2); }
    ;
