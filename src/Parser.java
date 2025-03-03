
public class Parser extends ParserEngine {
  public static void main(String[] args) {
    Parser p = new Parser();
    Node n= p.parser(p.readfile("in\\prog1.txt"));
    p.printNode(n);
    Design d=p.bldDesign(n);
    System.out.println(d);
    PrettyPrint.prettyprint(d);
  }

  Parser() {
    // This is a parser for the abstract syntax for Chisel programs
    //
    // lexical analysis
    // the lexer recognises identifiers, numbers and one character symbols as terminals
    // and will ignore comments
    // tokens match patterns but can appear in grammar rules.
    //
    setCommentStart("/*");
    setCommentEnd("*/");
    setLineComment("//");
    //
    addTokenPattern("<ident>", "[_a-zA-Z][_$a-zA-Z0-9]*");
    addTokenPattern("<string>", "\"(?:[^\"\\\\]++|\\\\.)*+\"");
    addTokenPattern("<number>", "\\d\\d*");
    //
    addTokens("++ -- && || == >= <= != <>");
    addTokens("+ - * / % = > < , . ; ( ) [ ] { }");
    addKeywords("const module int if printf for Mux void");
    addKeywords("valid ready Module val when outstream instream state read write goto");

    // -----------------------------------------------
    //
    //  Top-down parser with backtracking
    //
    // The parser engine allows a certain level of EBNF notation with "*", "+" and "?" after
    // nonterminals to denote zero-or-more, one-or-more, or zero-or-one repetitions.
    // A terminal symbol with spaces is considered a choice between several possible terminal strings
    //
    // Each rule has a semantic action where a parse tree is build as Node objects
    // the semantic action is a function of an array of nodes to a node
    // The default semantic action is to create a parse tree with the left-hand side as tag and
    // the right-hand side as children in the node structure
    //
    // The parser will construct an abstract sysntax tree as a Node structure.
    //
    // The node structure is then converted into Record objects with tags in nodes
    // expected to be names of record declarations in the AbsSyn java file
    // The 'Nodes.java' file contains a method 'mkRecord' that uses reflection to find
    // constructors for record declarations.
    //
    // -----------------------------------------------
    //  ⟨program⟩ ::= ⟨module⟩+⟨connnection⟩* ⟨module-decl ⟩+
    //
    rule("<program>", list("<mdef>*", "<conc>*", "<mdecl>*"),
        a -> node("Design", a[0], a[1], a[2]));
    //
    //  ⟨module⟩ ::= ‘val’ ⟨ident⟩ ‘=’ ‘Module’ ‘(’ ⟨ident⟩ ‘)’
    //  ⟨connection⟩ ::= ⟨ident⟩ ‘.’ ⟨ident⟩ ‘<>’ ⟨ident⟩ ‘.’ ⟨ident⟩
    //  ⟨module-decl ⟩ ::= ‘module’ ⟨ident⟩ ⟨declaration⟩* ⟨state⟩+
    //
    rule("<mdef>", list("val", "<ident>", "=", "Module", "(", "<ident>", ")"),
        a -> node("ValDecl", a[1], a[5]));
    rule("<conc>", list("<ident>", ".", "<ident>", "<>", "<ident>", ".", "<ident>"),
        a -> node("Conc", a[0], a[2], a[4], a[6]));
    rule("<mdecl>", list("module", "<ident>", "<decl>*", "<statedef>*"),
        a -> node("Module", a[1], flatList(a[2]), a[3]));
    //
    // -----------------------------------------------
    //  ⟨declaration⟩ ::= ‘int’ ⟨ident⟩ [ ‘=’ ⟨number⟩ ]
    //  | ‘int’ ‘[’ ⟨number⟩ ‘]’ ⟨ident⟩
    //  | ‘instream’ ⟨ident⟩
    //  | ‘outstream’ ⟨ident⟩
    //
    //
    rule("<decl>", list("int", "<ident>", "<init>?", "<xdecl>*"),
        a -> cons(node("VarDecl", a[1], mkinit(a[2],0)), a[3]));
    rule("<decl>", list("int", "[", "<number>", "]", "<ident>"),
        a -> node("ArrDecl", a[4], a[2]));
    rule("<decl>", list("instream", "<ident>"),
        a -> node("InDecl", a[1]));
    rule("<decl>", list("outstream", "<ident>"),
        a -> node("OutDecl", a[1]));
    //
    rule("<init>", list("=", "<exp>"),a->a[1]);
    rule("<xdecl>", list(",", "<ident>", "<init>?" ),
        a-> node("VarDecl", a[1], mkinit(a[2],0)) );
    //
    // -----------------------------------------------
    // ⟨state⟩ ::= ‘state’ ⟨number⟩ [ ‘when’ ⟨expr⟩ ] ⟨statement⟩* ‘goto’ ⟨gotoexp⟩
    // ⟨gotoexp⟩ ::= ⟨number⟩
    //  | ‘Mux’ ‘(’ ⟨expr⟩ ‘,’ ⟨gotoexp⟩ ‘,’ ⟨gotoexp⟩ ‘)’
    //
    rule("<statedef>", list("state", "<number>", "<whenpart>?", "<stat>*", "goto", "<exp>"),
        this::mkState);
        //a -> node("State", a[1], a[2], a[3], a[5]));
    rule("<whenpart>", list("when", "<bexp>"), a -> a[1]);
    //
    // -----------------------------------------------
    //  ⟨statement⟩ ::= ⟨ident⟩ ‘=’ ⟨expr⟩
    //    | ⟨ident⟩ ‘[’ ⟨expr⟩ ‘]’ ‘=’ ⟨expr⟩\
    //    | ⟨ident⟩ ‘=’ ⟨ident⟩ ‘[’ ⟨expr⟩ ‘]’
    //    | ⟨ident⟩ ‘.’ ‘write’ ‘(’ ⟨expr⟩ ‘)’
    //    | ⟨ident⟩ ‘=’ ⟨ident⟩ ‘.’ ‘read’ ‘(’ ‘)’

    rule("<stat>", list("<ident>", "=", "<ident>", ".", "read", "(", ")"),
        a -> node("ReadCh", a[0], a[2]));
    rule("<stat>", list("<ident>", "=", "<ident>", "[", "<exp>", "]"),
        a -> node("ReadMem", a[0], a[2], a[4]));
    rule("<stat>", list("<ident>", ".", "write", "(", "<exp>", ")"),
        a -> node("WriteCh", a[0], a[4]));
    rule("<stat>", list("<ident>", "=", "<exp>"),
        a -> node("Asg", a[0], a[2]));
    rule("<stat>", list("<ident>", "[", "<exp>", "]", "=", "<exp>"),
        a -> node("AsgMem", a[0], a[2], a[5]));

    // -----------------------------------------------
    //  ⟨expr⟩ ::= ⟨ident⟩
    //    | ⟨number⟩
    //    | ⟨expr⟩ ⟨operation⟩ ⟨expr⟩
    //    | ‘Mux’ ‘(’ ⟨expr⟩ ‘,’ ⟨expr⟩ ‘,’ ⟨expr⟩ ‘)’\
    //    | ⟨ident⟩ ‘.’ ‘ready’
    //    | ⟨ident⟩ ‘.’ ‘valid’
    //  ⟨operation⟩ ::= ‘+’ | ‘-’ | ‘*’ | ‘/’ | ‘%’
    //    | ‘&’ | ‘|’ | ‘>’ | ‘<’ | ‘>=’ | ‘<=’| ‘==’ | ‘!=’
    //
    rule("<bexp>", list("<exp>", "<bexp1>*"),this::mkBin);
    rule("<bexp1>", "== >= <= != > < && ||", "<exp>");
    //
    rule("<exp>",list("<trm>", "<exp1>*"),this::mkBin);
    rule("<exp1>","+ -", "<trm>");
    //
    rule("<trm>", list("<fld>", "<trm1>*"),this::mkBin);
    rule("<trm1>", "* / %", "<fld>");

    // -----------------------------------------------
    //
    rule("<fld>", list("Mux", "(", "<bexp>", ",", "<exp>", ",", "<exp>", ")"),
        a -> node("Mux", a[2], a[4], a[6]));
    rule("<fld>", list("<ident>", ".", "ready", "(", ")"), a -> node("Ready", a[0]));
    rule("<fld>", list("<ident>", ".", "valid", "(", ")"), a -> node("Valid", a[0]));
    //rule("<fld>", list("<ident>", "[", "<exp>","]"), a -> node("Idx", a[0],a[2]));
    rule("<fld>", list("<ident>" ), a -> node("Var", a[0]));
    rule("<fld>", list("<number>" ), a -> node("Num", a[0]));
    rule("<fld>", list("(", "<bexp>", ")"), a -> a[1]);
    //
    // -----------------------------------------------
    //
    verifyGrammar();
    // check that all terminals are defined as tokens, patterns or keywords
    // check that all nonterminals are defined as rules
    // check that nonterminals are not terminals
  }
  // helper function for semantic actions
  Node mkState(Node[] a){return node("State",a[1],mkinit(a[2],1),a[3],exp2goto(a[5]));}

  Node exp2goto(Node n) {
    if(!isGoto(n))fail("not goto "+n);
    if(n.h().equals("Num"))return new Node("Next",n.lst());
    if(n.h().equals("Mux")&&n.size()==3)
      return node("Cond",n.get(0),exp2goto(n.get(1)),exp2goto(n.get(2)));
    throw new RuntimeException("exp2goto "+n);
  }
  boolean isGoto(Node n) {
    if(n==null)return false;
     if(n.h().equals("Num"))return true;
     if(!n.h().equals("Mux"))return false;
     return isGoto(n.get(1))&&isGoto(n.get(2));
  }

  Node mkinit(Node n,int i){
    if(isAtom(n))return node("Num",node(""+i)); else return n.get(0);
  }

  Node mkBin(Node[] a){return mkBin(a[0],a[1]);}
  Node mkBin(Node n1,Node n2){
    if(n2==null)return n1;
    if(!isList(n2))return node("bin",n1,n2);
    if(length(n2)==0)return n1;
    Node n3=head(n2), n4=tail(n2);
    String opr=n3.get(0).h();
    if(opr.equals("&&"))opr="&";
    if(opr.equals("||"))opr="|";
    Node n5=node("Bin",node(opr),n1,n3.get(1));
    return mkBin(n5,n4);
  }

  //---------------------------------------------------------------------
  //
  Design bldDesign(Node n){return (Design) Nodes.mkRecord(n);}
  static Design parseDesign(String file){Parser p=new Parser();
    return p.bldDesign(p.parser(p.readfile(file)));
  }
}
