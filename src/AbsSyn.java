import java.util.ArrayList;
//-----------------------------------------------------------------
//
//  Abstract Syntax for CoreChisel
//
/*
    ⟨program⟩ ::= ⟨module⟩+ ⟨connnection⟩* ⟨module-decl ⟩+
    ⟨module⟩ ::= ‘val’ ⟨ident⟩ ‘=’ ‘Module’ ‘(’ ⟨ident⟩ ‘)’
    ⟨connection⟩ ::= ⟨ident⟩ ‘.’ ⟨ident⟩ ‘<>’ ⟨ident⟩ ‘.’ ⟨ident⟩
    ⟨module-decl ⟩ ::= ‘module’ ⟨ident⟩ ⟨declaration⟩* ⟨state⟩+
    ⟨declaration⟩ ::= ‘int’ ⟨ident⟩ [ ‘=’ ⟨number⟩ ]
      | ‘int’ ‘[’ ⟨number⟩ ‘]’ ⟨ident⟩
      | ‘instream’ ⟨ident⟩\
      | ‘outstream’ ⟨ident⟩
    ⟨state⟩ ::= ‘state’ ⟨number⟩ [ ‘when’ ⟨expr⟩ ] ⟨statement⟩* ‘goto’ ⟨gotoexp⟩
    ⟨statement⟩ ::= ⟨ident⟩ ‘=’ ⟨expr⟩
      | ⟨ident⟩ ‘[’ ⟨expr⟩ ‘]’ ‘=’ ⟨expr⟩\
      | ⟨ident⟩ ‘=’ ⟨ident⟩ ‘[’ ⟨expr⟩ ‘]’
      | ⟨ident⟩ ‘.’ ‘write’ ‘(’ ⟨expr⟩ ‘)’
      | ⟨ident⟩ ‘=’ ⟨ident⟩ ‘.’ ‘read’ ‘(’ ‘)’
    ⟨expr⟩ ::= ⟨ident⟩
      | ⟨number⟩
      | ⟨expr⟩ ⟨operation⟩ ⟨expr⟩
      | ‘Mux’ ‘(’ ⟨expr⟩ ‘,’ ⟨expr⟩ ‘,’ ⟨expr⟩ ‘)’\
      | ⟨ident⟩ ‘.’ ‘ready’
      | ⟨ident⟩ ‘.’ ‘valid’
    ⟨operation⟩ ::= ‘+’ | ‘-’ | ‘*’ | ‘/’ | ‘%’
      | ‘&’ | ‘|’ | ‘>’ | ‘<’ | ‘>=’ | ‘<=’| ‘==’ | ‘!=’
    ⟨gotoexp⟩ ::= ⟨number⟩
      | ‘Mux’ ‘(’ ⟨expr⟩ ‘,’ ⟨gotoexp⟩ ‘,’ ⟨gotoexp⟩ ‘)’
*/

public class AbsSyn { } // not used file contains record declarations

record Design(ArrayList<ValDecl> decl, ArrayList<Conc> con, ArrayList<Module> mod ){}

record ValDecl(String lhs,String rhs){
  public String toString(){return "val "+lhs+" = Module("+rhs+")";}}
record Conc(String m1,String out,String m2,String in){
  public String toString(){return m1+"."+out+" <> "+m2+"."+in;}}
record Module(String nm,ArrayList<Decl> decl,ArrayList<State> states){
  public String toString(){return "module "+nm+" "+decl+""+states;}}
record State(int n,Exp cmd,ArrayList<Stat> stm, Goto g){
  public String toString(){return "state"+" "+n+" when "+cmd+" "+stm+" goto "+g;}}

interface Decl{}
record VarDecl(String nm,Exp init) implements Decl{
  public String toString(){return "int"+" "+nm+" = "+init;}}
record ArrDecl(String nm,int idx) implements Decl{
  public String toString(){return "int["+idx+"] "+nm;}}
record InDecl(String nm) implements Decl{
  public String toString(){return "instream "+nm;}}
record OutDecl(String nm) implements Decl{
  public String toString(){return "outstream "+nm;}}

interface Exp{}
record Bin (String cmd, Exp e1,Exp e2) implements Exp{
  public String toString(){return par(e1)+" "+cmd+" "+par(e2);}
  private String par(Exp e){return (e instanceof Bin)?"("+e+")":""+e; }}
record Var (String nm) implements Exp{
  public String toString(){return nm;}}
record Num (int i) implements Exp{
  public String toString(){return ""+i;}}
record Mux(Exp e0,Exp e1,Exp e2) implements Exp{
  public String toString(){return "Mux("+e0+","+e1+","+e2+")";} }
record Ready(String s) implements Exp{
  public String toString(){return s+".ready()";} }
record Valid(String s) implements Exp{
  public String toString(){return s+".valid()";} }

interface Stat{}
record Asg (String lhs, Exp rhs) implements Stat{
  public String toString(){return lhs+" = "+rhs ;}}
record AsgMem (String lhs, Exp idx, Exp rhs) implements Stat{
  public String toString(){return lhs+"["+idx+"] = "+rhs ;}}
record ReadMem (String lhs, String rhs, Exp idx) implements Stat{
  public String toString(){return lhs+" = "+rhs+"["+idx+"]";}}
record ReadCh (String lhs,String ch) implements Stat{
  public String toString(){return lhs+" = "+ch+".read()";}}
record WriteCh (String ch,Exp rhs) implements Stat{
  public String toString(){return ch+".write("+rhs+")";}}

interface Goto {}
record Next(int i) implements Goto{
  public String toString(){return ""+i;}}
record Cond(Exp e,Goto g1,Goto g2) implements Goto{
  public String toString(){return "Mux("+e+","+g1+","+g2+")";}}

