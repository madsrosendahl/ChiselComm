import java.io.*;
import java.util.*;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;



//---------------------------------------------------------------------------
//
//  Top-down parser and lexer with backtracking
//
// The grammar should be specified as grammar rules with a nonterminal on the left-hand side
// and a list of nonterminals and terminals on the right-hand side
// Parsing is done with attempting to recognize input according to the rules in order.
// Default semantic action for terminals is to return an atomoc Node with teh terminal
// Default semantic action for grammar rules is to create a node with the left-hand side
// nonterminal as tag and right-hand side nodes as children.
// The grammar rules can specify semantic actions as mapping of an array of nodes to a node.
//
// The lexical analysis as based on specification of tokens as strings
// and patterns for identifiers, numbers and strings.
// Keywords can be recognized as identifiers but should be declared as keywords so
// that terminal symbols that appear in the grammar are declared.
// The lexer will ignore comments
// The parser engine will destinguish between nonterminals in that must not be recognized
// by the parser as terminals. It will be checked that all nonterminals are declared in rules.
//
// The parse engine allows a certain level of EBNF notation with "*", "+" and "?" after
// nonterminals to denote zero-or-more, one-or-more, or zero-or-one repetitions.
// A terminal symbol with spaces is considered a choice between several possible terminal strings
//
// The grammar rules and lexer specification should be done in the constructor of a subclass
// The parser is called using the method "parser" that takes a list of input strings and parse
// according the start symbol (first non-terminal in the grammar)



record Rule(String lhs, List<String>rhs, Function<Node[], Node> f){
  public String toString(){return lhs +" -> "+(rhs==null?"[]":rhs);}
}
record ParseRes(int i1,int i2,String lhs,Node res){
  public String toString(){return lhs+"["+i1+":"+i2+"]" +" -> "+(res==null?"[]":res);}
}

//---------------------------------------------------------------------------

public class ParserEngine extends Nodes{//} extends Lexer{
  static boolean tst=false;
  private HashMap<String,ArrayList<Rule>> gram=new HashMap<>();
  private ArrayList<String> nonterm=new ArrayList<>();
  private HashMap<String,String> choiceTerm=new HashMap<>();
  private ArrayList<String> keywords =new ArrayList<>();
  //
  void rule(String lhs, List<String>rhs, Function<Node[], Node> f){
    if(!nonterm.contains(lhs)) nonterm.add(lhs);
    if(!gram.containsKey(lhs))gram.put(lhs,new ArrayList<Rule>());
    gram.get(lhs).add(new Rule(lhs,rhs,f));
    for(int i=0;i<rhs.size();i++){
      String rh0=rhs.get(i),rh1=spaceTerm(rh0);
      addEBNF(rh0);
      if(rh0!=rh1)rhs.set(i,rh1);
    }
  }
  // default rule creates a parse tree with lhs as node tag
  void rule(String lhs,List<String> rhs){
    rule(lhs,rhs,a->node(lhs,a));
  }
  // default rule creates a parse tree with lhs as node tag
  void rule(String lhs,String ...rhs){
    ArrayList<String> rhs1=new ArrayList<>();
    rhs1.addAll(Arrays.asList(rhs));
    rule(lhs,rhs1,a->node(lhs,a));
  }
  static ArrayList<String> list(String ... lst){
    ArrayList<String> ret=new ArrayList<>();
    for(String x:lst)ret.add(x);
    return ret;
  }
  // you can use postfix operators "*". "+", and "?" on nontermials in EBNF style
  void addEBNF(String rh){
    if(rh.length()==1||!Character.isAlphabetic(rh.charAt(1)))return;
    if(!rh.endsWith("*")&&!rh.endsWith("+")&&!rh.endsWith("?"))return;
    if(nonterm.contains(rh))return;
    String rh0=rh.substring(0,rh.length()-1);
    if(rh.endsWith("*")){
      //System.out.println("got "+rh);
      rule(rh,list(rh0,rh),a->cons(a[0],a[1]));
      rule(rh,list(),a->node("empty"));
    }
    if(rh.endsWith("+")){
      //System.out.println("got "+rh);
      rule(rh,list(rh0,rh0+"*"),a->cons(a[0],a[1]));
    }
    if(rh.endsWith("?")){
      //System.out.println("got "+rh);
      rule(rh,list(rh0),a->node("list",a[0]));
      rule(rh,list(),a->node("empty"));
    }
  }
  // you can use a space in terminals to indicate a choice between different options
  String spaceTerm(String rh0) {
    if(!rh0.contains(" "))return rh0;
    if(choiceTerm.containsKey(rh0))return choiceTerm.get(rh0);
    String rh1="T("+rh0.replace(' ','|')+")";
    choiceTerm.put(rh0,rh1);
    //System.out.println("got "+rh1);
    String[] trms = rh0.split(" ");
    for(String trm:trms) rule(rh1,list(trm),a->a[0]);
    return rh1;
  }
  //-----------------------------------------------------
  // parse a sequence of tokens starting at index "i"  in list "l"
  // according to nonterminal "lhs"
  public ParseRes parse(String lhs, List<String> l, int i) {
    //System.out.println();
    String lk0=i<l.size()?l.get(i):"$";
    if(tst)System.out.println("parse:"+i+" "+lhs+" at "+lk0);
    ArrayList<Rule> rs=gram.get(lhs);
    if(rs==null){ System.out.println("unknown nt "+lhs);return null; }
    lab1:
    for(Rule r:rs){
      ArrayList<ParseRes> rmtch=new ArrayList<>();
      List<String> rhs=r.rhs();
      Node[] nodes=new Node[rhs.size()];
      int ix=i,sz=rhs.size();
      if(tst)System.out.println("Try "+rule2string(r));
      if(sz>0&&rhs.get(0).equals("<error>")) {
        System.out.println("Error detection: "+lk0);
        ArrayList<Node> m=new ArrayList<>();
        String tk1 =rhs.get(1);
        System.out.println("search for "+tk1);
        while(ix<l.size()-1&&!l.get(ix).equals(tk1)){ m.add(node(l.get(ix)));ix++;}
        System.out.println("found "+m);
        ParseRes xx= new ParseRes(i,ix,lhs,new Node("<error>",m));
        if(tst)System.out.println(">"+xx);
        return xx;
      }
      for(int j=0;j<rhs.size();j++){
        String tk=rhs.get(j);
        String lk=ix<l.size()?l.get(ix):"$";
        if(ix>=l.size())continue;
        if(tst)System.out.println("try:"+ix+"  "+tk+" at "+lk);
        //for(String tk:r.rhs()){
        if(gram.containsKey(tk)){
          ParseRes res=parse(tk,l,ix);
          if(res==null)continue lab1;
          ix= res.i2();
          rmtch.add(res);
          nodes[j]= res.res();
        }else if(isPattern(tk)) {
          String tk1=l.get(ix);
          if(matchPattern(tk,tk1)){
            ix++;
            rmtch.add( new ParseRes(ix-1,ix,tk1,null));
            nodes[j]= new Node(tk1,null);
          }else continue lab1;
        }else{
          if(ix>=l.size()) continue lab1;
          String tk1=l.get(ix);
          if(matchTerminal(tk,tk1)){
            ix++;
            rmtch.add( new ParseRes(ix-1,ix,tk1,null));
            nodes[j]= new Node(tk1,null);
            //rhs.add(new Token(tk));
          }else continue lab1;
        }
      }
      ParseRes xx= new ParseRes(i,ix,lhs,r.f().apply(nodes));
      if(tst)System.out.println(">"+xx);
      return xx;
    }
    if(tst)System.out.println("fail:"+i+" "+lhs+" : "+lk0);
    return null;
  }

  private boolean matchTerminal(String tk, String s) {
    boolean res=false;
    if(tk.equals("ident"))
      res =Character.isAlphabetic(s.charAt(0));
    else if(tk.equals("number"))
      res =Character.isDigit(s.charAt(0));
    else
      res=tk.equals(s);
    //System.out.println("check term "+tk+" "+s+"  "+res);
    return res;
  }

  //---------------------------------------------------------------------
  // parse list, string, file to a node tree

  Node parser( List<String> lst) {
    return parser(nonterm.get(0),lst);
  }
  Node parser(String nt, List<String> lst) {
    ArrayList<String> tks = tokenize(lst);
    ParseRes pr=parse(nt,tks,0);
    if(pr.i2()==tks.size()) return pr.res();
    System.out.println("ParseRes "+pr.i1()+" "+pr.i2()+" "+tks.size()+" "+pr.lhs());
    for(int i=pr.i2();i<tks.size()&&i<pr.i2()+5;i++)
      System.out.print(tks.get(i)+" ");
    System.out.println();
    return pr.res();
  }

  //--------------------------------------------------------------------------------
  // check that all terminals are defined as tokens, patterns or keywords
  // check that all nonterminals are defined as rules
  // check that nonterminals are not terminals
  //
  void verifyGrammar(){
    HashSet<String> nonterm=new HashSet<>();
    for(String lh:gram.keySet())nonterm.add(lh);
    for(String lh:nonterm){
      if(isToken(lh)){
        System.out.println("bad nonterminal "+lh);
      }
      for(Rule r:gram.get(lh)){
        for(String str:r.rhs()){
          if(nonterm.contains(str))continue;
          if(isToken(str))continue;
          if(isPattern(str))continue;
          if(keywords.contains(str))continue;
          if(str.equals("<error>"))continue;
          System.out.println("Not terminal or nonterminal "+str+ " in "+r);
        }
      }
    }
  }

  //--------------------------------------------------------------------------
  // pretty printer for grammars
  void showGrammar(){
    for(String lhs:nonterm){
      for(Rule rule:gram.get(lhs))
        System.out.println(rule2string(rule));
      System.out.println();
    }
  }
  // for pretty printing grammar
  String rhs2string(List<String> rhs){
    String ln= "";
    for(String tk: rhs) ln+=" "+tk;
    return ln;
  }
  String rule2string(Rule rule){
    return rule.lhs()+" ::="+rhs2string(rule.rhs());
  }

  // ------------------------------------------------------------------------------------
  public static void writefile(ArrayList<String> list, String f){
    try{
      PrintWriter out=new PrintWriter(new FileWriter(f));
      for(String s:list){
        out.println(s);
      }
      out.close();
    }catch(IOException e){
      System.out.println("error "+e);
    }
  }

  public static ArrayList<String> readfile(String f){
    ArrayList<String> list=new ArrayList<>();
    try{
      BufferedReader in=new BufferedReader(new FileReader(f));
      while(true){
        String s=in.readLine();
        if(s==null)break;
        list.add(s);
      }
      in.close();
    }catch(IOException e){
      return null;
    }
    return list;
  }

// ------------------------------------------------------------------------------------
//
//  Lexxer part of ParserEngine

  private String comStart="/*";
  private String comEnd="*/";
  private String comLine="//";
  //
  void setCommentStart(String s) {comStart=s; }
  void setCommentEnd(String s) {comEnd=s;   }
  void setLineComment(String s) { comLine=s; }
  //
  //----------------------------------------------
  // define patterns
  private String pattern=null;
  private Pattern patmat =null;
  private HashMap<String,Pattern> nonterm2pattern=new HashMap<>();
  private ArrayList<String> tokens=new ArrayList<>();
  //
  void addToken(String s){
    String s1="";
    for(int i=0;i<s.length();i++)s1+="[\\"+s.charAt(i)+"]";
    tokens.add(s);
    addPattern(s1);
  }
  void addTokens(String s) {
    for(String s1:s.split(" "))addToken(s1);
  }
  void addPattern(String s){
    String s1="(?:"+s+")";
    if(pattern==null)pattern=s1; else pattern=pattern+"|"+s1;
  }
  String getToken(String s){
    if(patmat==null){
      //System.out.println("pattern "+pattern);
      patmat=Pattern.compile(pattern);
    }
    Matcher m=patmat.matcher(s);
    if(m.lookingAt()){
      String r = s.substring(0, m.end());
      return r;
    }
    return s.substring(0,1);
  }
  void addTokenPattern(String s, String s1) {
    addPattern(s1);
    nonterm2pattern.put(s,Pattern.compile(s1));
    //System.out.println(s+" "+s1);
  }
  boolean isPattern(String s) {return nonterm2pattern.containsKey(s);}
  boolean matchToken(String s){
    String r=getToken(s);
    return s.equals(r);
  }
  boolean isToken(String s){
    return tokens.contains(s);
  }
  boolean matchPattern(String tk,String tk1){
    Pattern p=nonterm2pattern.get(tk);
    if(p==null)return false;
    Matcher m=p.matcher(tk1);
    boolean lk=m.lookingAt(); int mend=lk?m.end():0;
    //System.out.println("match "+tk+" "+tk1+ " "+lk+" "+mend);
    return lk&& mend==tk1.length();
  }
  ArrayList<String> tokenize(List<String> in){
    if(in==null)fail("tokenize on null list");
    ArrayList<String> ret = new ArrayList<>();
    boolean inCom=false;
    for(String s:in){
      String t=s.trim();
      for(;;){
        if(inCom){
          //System.out.println("in Comm "+t);
          if(!t.contains(comEnd)){break;}
          int endc=t.indexOf(comEnd)+2;
          t=t.substring(endc).trim();
          //System.out.println("comm end "+endc+" "+t);
          inCom=false; continue;
        }
        if(t.startsWith(comStart)){
          t=t.substring(2);
          if(!t.contains(comEnd)){inCom=true; break;}
          int endc=t.indexOf(comEnd)+2;
          t=t.substring(endc).trim();
          //System.out.println("comm end "+endc+" "+t);
          inCom=false; continue;
        }
        if(t.startsWith(comLine))break;
        if(t.length()==0)break;
        String tk=getToken(t);
        ret.add(tk);
        t=t.substring(tk.length()).trim();
      }
    }
    return ret;
  }
  void addKeywords(String s){
    for(String t:s.split(" "))keywords.add(t);
  }
}