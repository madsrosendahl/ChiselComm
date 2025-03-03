// This class contains a prettyprinter for CoreChisel abstract syntax
// as described by the constructors in the AbsSyn file
// most of the

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;

public class PrettyPrint {
  public static void main(String[] args) {
    Design d=Parser.parser("src\\in\\prog9.txt");
    String t="src\\out\\tmp.txt";
    PrettyPrint.prettyprint(d,t);
    for(String s:InOut.readfile(t)) System.out.println(s);
  }

  //-------------------------
  // The class contains a method prettyprint to print a design in the abstract syntax

  public static void prettyprint(Design d){
    PrettyPrint p=new PrettyPrint();
    p.pp(System.out,d);
  }
  public static void prettyprint( Design d,String f){
    PrettyPrint p=new PrettyPrint();
    PrintStream out=InOut.outfile(f);
    p.pp(out,d);
    out.close();
  }
  //-------------------------
  private PrettyPrint(){}

  private void pp(PrintStream out, Design d){
    for(ValDecl vd:d.decl())pp(out,vd);
    for(Conc cn:d.con())pp(out,cn);
    out.println();
    for(Module m:d.mod())pp(out,m);
  }
  private void pp(PrintStream out,ValDecl vd){
    out.println(vd);
  }
  private void pp(PrintStream out,Conc cn){
    out.println(cn);
  }
  private void pp(PrintStream out,Module m){
    out.println("module "+m.nm());
    for(Decl d: m.decl())pp(out,d);
    for(State s: m.states())pp(out,s);
  }
  private void pp(PrintStream out,Decl d){
    out.println(d);
  }

  private void pp(PrintStream out,State s){
    if(s.cmd().equals(new Num(1)))
      out.println("state "+s.n());
    else
      out.println("state "+s.n()+" when "+s.cmd());
    for(Stat st:s.stm())pp(out,st);
    out.println("  goto "+s.g());
    out.println();
  }

  private void pp(PrintStream out,Stat s){
    out.println("  "+s);
  }
}
