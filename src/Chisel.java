import javax.swing.*;
import java.io.*;
import java.util.*;
public class Chisel{
  public static void main(String[] args) {
    System.out.println("Hello");
    Design d=Parser.parseDesign("src\\in\\prog8.txt");
    Chisel.toChisel(d,"Main8");
  }

  public static void toChisel(Design d,String main){
    Chisel chisel=new Chisel();
    chisel.toChisel(d,System.out,main);
  }
  public static void toChisel(Design d,String main,String f){
    PrintStream out= Interpreter.outfile(f);
    Chisel chisel=new Chisel();
    chisel.toChisel(d,out,main);
    out.close();
  }

//------------------------------------------------------------

  private void toChisel(Design d,PrintStream out,String main){
    out.println(
        "import Chisel.switch\n" +
        "import chisel3._\n" +
        "import chisel3.util.{DecoupledIO, is}\n\n" +
        "class "+main+" extends Module {");
    for(ValDecl vd:d.decl()){
      out.println("  val "+vd.lhs()+" = Module(new "+vd.rhs()+"())");
    }
    for(Conc cn:d.con()){
      out.println("  "+cn.m1()+".io."+cn.out()+" <> "+cn.m2()+".io."+cn.in());
    }
    out.println("}");
    for(Module m:d.mod())toChisel(m,out);
  }
  private void toChisel(Module m,PrintStream out){
    // split declarations into io, memory banks and registers
    ArrayList<InDecl> id=new ArrayList<>();
    ArrayList<OutDecl> od=new ArrayList<>();
    ArrayList<ArrDecl> mb=new ArrayList<>();
    ArrayList<VarDecl> rg=new ArrayList<>();
    for(Decl d:m.decl()){
      switch(d){
        case InDecl d1 ->{id.add(d1);}
        case OutDecl d1 ->{od.add(d1);}
        case ArrDecl d1 ->{mb.add(d1);}
        case VarDecl d1 ->{rg.add(d1);}
        default -> {Aux1.fail("toChisel");}
      }
    }
    out.println();
    out.println("class "+m.nm()+" extends Module{");
    if(id.size()>0||od.size()>0){
      out.println("  val io = IO(new Bundle{");
      for(OutDecl d:od)
        out.println("    val "+d.nm()+" = new DecoupledIO(UInt(32.W))");
      for(InDecl d:id)
        out.println("    val "+d.nm()+" = Flipped(new DecoupledIO(UInt(32.W)))");
      out.println("  })");
      for(OutDecl d:od) {
        out.println("  val "+d.nm()+"Bits = Reg(UInt(32.W))");
        out.println("  val "+d.nm()+"Valid = RegInit(false.B)");
        out.println("  io."+d.nm()+".bits := "+d.nm()+"Bits");
        out.println("  io."+d.nm()+".valid := "+d.nm()+"Valid");
        out.println("  when(io."+d.nm()+".ready === 0.B) { "+d.nm()+"Valid := 0.B }");
      }
      for(InDecl d:id) {
        out.println("  val "+d.nm()+"Ready = RegInit(false.B)");
        out.println("  io."+d.nm()+".ready := "+d.nm()+"Ready");
        out.println("  when(io."+d.nm()+".ready === 0.B) { "+d.nm()+"Ready := 1.B }");
      }
    }
    ArrayList<ReadMem> rm= getMemR(m.states());
    for(VarDecl r:rg)toChisel(r,out,rm);
    for(ArrDecl a:mb)toChisel(a,out,rm);
    out.println("  val stateReg = RegInit(1.U(8.W))");
    mkprint(m.nm(),mb,rg,od,out);

    toChisel(m.states(),out);
    out.println("  }");
    out.println("}");
  }

  private void mkprint(String nm,ArrayList<ArrDecl> mb, ArrayList<VarDecl> rg, ArrayList<OutDecl> od, PrintStream out) {
    String r1= "  printf(\""+nm+" %d";
    String r2= ",stateReg";
    for(VarDecl v:rg){r1+=" %d:"+v.nm()+""; r2+=","+v.nm();}
    out.println(r1+"\\n\""+r2+")");
    for(OutDecl o: od) {
      out.println("  printf(\"Channel %d:bits %d:ready %d:valid\\n\","
        + o.nm() + "Bits, io." + o.nm() + ".ready, " + o.nm() + "Valid)");
    }
  }

  private void toChisel(VarDecl r,PrintStream out,ArrayList<ReadMem> rm) {
    for(ReadMem r1:rm)if(r1.lhs().equals(r.nm()))return;
    out.println("  val "+r.nm()+" = RegInit("+e2ch(r.init())+"(32.W))");
  }
  private void toChisel(ArrDecl a,PrintStream out,ArrayList<ReadMem> rm) {
    String nm= a.nm();
    String rd="xx";
    for(ReadMem rr:rm){
      if(nm.equals(rr.rhs()))rd=rr.lhs();
    }
    out.println("  val "+nm+" = SyncReadMem("+a.idx()+", UInt(32.W))");
    out.println("  val "+nm+"ReadAddr = WireInit(0.U)");
    out.println("  val "+rd+" = "+nm+".read("+nm+"ReadAddr)");
  }
  private ArrayList<ReadMem> getMemR(ArrayList<State> states) {
    ArrayList<ReadMem> lst=new ArrayList<>();
    for(State s:states)for(Stat s1:s.stm()){
      switch (s1){case ReadMem r ->{lst.add(r);} default ->{}}
    }
    return lst;
  }

  private void toChisel(ArrayList<State> m,PrintStream out) {
    out.println("  switch(stateReg) {" );
    for(int i=0;i<m.size();i++){
      State s=m.get(i); Exp c=s.cmd(); boolean hasC=!(c instanceof Num);
      out.println("    is("+s.n()+".U){" );
      if(hasC)out.println( "      when("+e2ch(c)+"){");
      for(Stat s1:s.stm())toChisel(s1,out);
      out.println( "        stateReg := "+g2ch(s.g()));
      if(hasC)out.println( "      }");
      out.println( "    }");
    }
  }
  private void toChisel(Stat s,PrintStream out) {
    String idx="        ";
    switch(s){
      case Asg a ->{out.println(idx+a.lhs()+" := "+e2ch(a.rhs()));}
      case AsgMem am->{out.println(idx+am.lhs()+".write("+e2ch(am.idx())+","+e2ch(am.rhs())+")");}
      case ReadMem rm->{out.println(idx+rm.rhs()+"ReadAddr := "+e2ch(rm.idx()));}
      case ReadCh rc ->{out.println(idx+rc.ch()+"Ready :=0.B");
        out.println(idx+rc.lhs()+" := io."+rc.ch()+".bits");}
      case WriteCh wc ->{out.println(idx+wc.ch()+"Valid :=1.B");
        out.println(idx+wc.ch()+"Bits := "+e2ch(wc.rhs()));}
      default -> { System.out.println("stat "+s);}
    }
  }
  private String g2ch(Goto g) {
    switch(g){
      case Next n -> {return n+".U"; }
      case Cond c -> {return "Mux("+e2ch(c.e())+","+g2ch(c.g1())+","+g2ch(c.g2())+")";}
      default -> { return null;}
    }
  }
  private String e2ch(Exp e) {
    switch(e){
      case Num n->{return n+".U";}
      case Var v->{return v.nm();}
      case Bin b->{return e2ch(b.e1())+" "+b.cmd()+" "+e2ch(b.e2());}
      case Mux m -> {return "Mux("+e2ch(m.e0())+","+e2ch(m.e1())+","+e2ch(m.e2())+")";}
      case Valid v -> {return v.s()+"Ready === 1.B && io."+v.s()+".valid === 1.B";}
      case Ready v -> {return v.s()+"Valid === 0.B && io."+v.s()+".ready === 1.B";}
      default -> { }
    }
    System.out.println("Err Exp "+e);
    return e.toString();
  }
}
