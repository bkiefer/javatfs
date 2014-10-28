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

%define parser_class_name "TdlParser"

%code {
/* This is a first attempt at building a TDL parser for the LKB subset
   in Java
 */

}

%token < String >  ID

 /*
%type < Match > expr term feature nominal id_lvar iv_expr iv_term
%type < DagNode > rexpr rterm rfeat r_id_var rnominal rarg
%type < Path > path
 */

%%

typedefs : typedef typedefs { }
         | typedef
         ;

typedef : ID ":=" nodes { }
        | ID ":<" types { }
        | ID ":+" nodes { }
        ;

types : ID '&' types { }
      | ID {}
      ;

nodes : node '&' nodes { }
      | node
      ;

node : ID { }
     | '[' featvals ']' { }
     | '#' ID { }
     | '<' elements '>' { }
     | "<!" elements "!>" { }
     | '<' '>' { }
     | "<!" "!>" { }
     ;

featvals : featval ',' featvals { }
         | featval { }
         ;

featval : path nodes { }
        ;

path : ID '.' path { }
     | ID { }
     ;

elements : nodes ',' elements { }
         | nodes { }
         | "..." { }
         ;
