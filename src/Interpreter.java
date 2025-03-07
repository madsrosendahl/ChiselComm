
import java.io.*;
import java.util.*;

//--------------------------------------------------------------------------
// data type for environments with pretty printer
// pretty printer for environment includes newline after each four elements
//
record EnvC(TreeMap<String,Integer> map){
  public String toString(){
    String r="{"; int i=0;
    for(String k:map.keySet()){
      if(i>0)r=r+", ";
      if(i%4==0&&i>0)r=r+"\n ";
      r=r+"("+k+")="+map.get(k);
      i++;
    }
    return r+"}"; }
}

//--------------------------------------------------------------------------
// Interpreter for chisel designs
//

public class Interpreter extends Aux1{
  public static void main(String[] args) {
    Design d = Parser.parseDesign("in\\prog8.txt");
    //PrettyPrint.prettyprint(d);
    Interpreter.interpreter(d,50);
    //Interpreter.interpreter(d,50,"out\\log8.txt");
  }
  static boolean showClock =true;
  static boolean showEnv =true;
  //-----------------------------------------------------------------
  // run interpreter on Design 'd' with maximum 'mx steps
  // and print output to file 'f'


  //--------------------------------------------------------------------------

  Interpreter(PrintStream out){this.out=out;}
  PrintStream out =null;
  ///*--------------------------------------------------------------------------
  // Construction of initial environment
  // I[[mod+con∗mdcl+]] = c[[con∗]] ⊕ m[[mod∗]](D[[mdcl∗]])
  // c[[con1 . . . conn]] = c[[con1]] 1 ⊕ · · · c[[con1]] n
  // c[[m1.out1’<>’m2.in2]] i = [(m1.out1) → i] ⊕ [(m2.in2) → i]⊕
  //   [(i, ’ready’) → 0] ⊕ [(i, ’valid’) → 0] ⊕ [(i, ’data’) → 0]⊕
  //   [(m1, c1) → i] ⊕ [(m2, c2) → i]
  // m[[mod1 · · · modn]] d = m[[mod1]] d ⊕ · · · ⊕ m[[modn]] d
  // m[[’val’m’=’’Module’’(’M’)’]]d = d M m

  EnvC initEnv(Design d){
    return addEnv(mm(d.decl(),d.mod()),cc(d.con()));
  }

  private EnvC mm(ArrayList<ValDecl> decl, ArrayList<Module> mod) {
    EnvC env0=null;
    for(ValDecl dl:decl)env0=addEnv(env0,mm(dl,mod));
    return env0;
  }
  private EnvC mm(ValDecl dl, ArrayList<Module> mod) {
    return dd(getMod(dl.rhs(),mod),dl.lhs());
  }
  private EnvC cc(ArrayList<Conc> con){
    EnvC env0=null;
    int n=1;
    for(Conc c:con){
      env0=addEnv(env0,mkEnv(n+",ready",0));
      env0=addEnv(env0,mkEnv(n+",valid",0));
      env0=addEnv(env0,mkEnv(n+",data",0));
      env0=addEnv(env0,mkEnv(c.m1() +","+c.out(),n));
      env0=addEnv(env0,mkEnv(c.m2() +","+c.in(),n));
      n++;
    }
    return env0;
  }
  //Declaration of registers in modules
  //  D[[mdcl1 . . . mdcln]] M m = D[[mdcl1]] M m ⊕ · · · ⊕ D[[mdcln]] M m
  //  D[[’module’M1decl states]] M m =if M = M1 then D[[decl]]m else⊥Σ
  //  D[[d1 · · · dn]] m = D[[d1]] m ⊕ D[[dn]] m ⊕ [(m, ’state’) → 1]
  //  D[[’int’x = n]] m = [(m, x) → n]
  //  D[[’int’[n]a]] m = [(m, a′0) → n] ⊕ · · · ⊕ [(m, a′(n − 1))) → n]

  EnvC dd(Module mod, String m) {
    EnvC env0=Aux1.mkEnv(m+",state",1);
    for(Decl d: mod.decl())env0=addEnv(env0,dd(d,m));
    return env0;
  }
  EnvC dd(Decl d, String m) {
    switch(d){
      case VarDecl v -> {return Aux1.mkEnv(m+","+v.nm(),ee(v.init(),null,null));}
      case ArrDecl v -> {EnvC env0=null;
        for(int i=0;i<v.idx();i++)env0=addEnv(env0,Aux1.mkEnv(m+","+v.nm()+"'"+i,0));
        return env0;
      }
      case InDecl v -> {return null;}  // set by declaration of connections
      case OutDecl v -> {return null;} // set by declaration of connections
      default -> {fail(); return null;}
    }
  }

  //*--------------------------------------------------------------------------
  //  Channel reset
  //    R[[con1 · · · conn]] σ = R[[con1]] σ ⊕ · · · ⊕ R[[conn]] σ
  //    R[[m1.out1’<>’m2.in2]] σ =let c = σ(m1, out1)
  //      if σ(c, ’ready’) = 0 then [(c, ’ready’) → 1, (c, ’valid’) → 0] else ⊥Σ

  EnvC rr(Design d,EnvC env){
    EnvC env0=null;
    for(Conc c:d.con()){
      int ch=getV(c.m1()+","+c.out(),env);
      if(getV(ch+",ready",env)==0)env0=addEnv(env0,mkEnv(ch+",ready",1,ch+",valid",0));
    }
    return env0;
  }
  ///*--------------------------------------------------------------------------
  // Transition function for modules and states
  //   T[[mod+con∗mdcl+]]σ = (Tm[[mod∗]](Td[[mdcl∗]]) σ) ⊕ R[[con∗]]σ
  //   Td[[mdcl1 · · · mdcln]] σ M m = Td[[mdcl1]] σ M m ⊕ · · · ⊕ Td[[mdcln]] σ M m
  //   Td[[’module’ M1 decl states]] σ M m =if M = M1 then Tt[[states]]σ m else ⊥Σ
  //   Tt[[state1 · · · staten]] σ m = Tt[[state1]]σ m ⊕ · · · ⊕ Tt[[staten]]σ m
  //   Tt[[’state’n’when’e s1 · · · sn’goto’eg]] σ m =
  //     if σ(m, ’state’)  ̸= n then ⊥Σ else
  //     if E[[e]] σ m ̸= 1 then ⊥Σ else
  //  Tt[[s1]] σ m ⊕ · · · ⊕ Tt[[sn]] σ m ⊕ [(m, ’state’) → E[[eg]] σ m]

  EnvC tt(Design d,EnvC env){
    EnvC env0= null;
    for(ValDecl v:d.decl())env0=addEnv(env0,td(v.lhs(),v.rhs(),d.mod(),env));
    return addEnv(env0,rr(d,env));
  }
  EnvC td(String lhs, String rhs, ArrayList<Module> mod, EnvC env) {
    Module mm=getMod(rhs,mod);
    return td(mm,env,lhs);
  }
  EnvC td(Module mod, EnvC env,String m) {
    return tt(mod.states(),env,m);
  }
  EnvC tt(ArrayList<State> sts,EnvC env,String m){
    int sn=Aux1.getV(m+",state",env);
    State s=getState(sn,sts);
    return tt(s,env,m);
  }
  EnvC tt(State s,EnvC env,String m){
    EnvC env0=null;
    if(ee(s.cmd(),env,m)!=1)return env0;
    for(Stat s1:s.stm())env0=addEnv(env0,ts(s1,env,m));
    env0=addEnv(env0,eg(s.g(),env,m));
    return env0;
  }
  EnvC eg(Goto g, EnvC env, String m) {
    switch(g){
      case Next n -> {return mkEnv(m+",state",n.i());}
      case Cond gt -> {return eg((ee(gt.e(),env,m)==1)?gt.g1():gt.g2(),env,m);}
      default ->{fail("eg");return null;}
    }
  }

  ///*--------------------------------------------------------------------------
  //Transition function for statements

  //   Ts[[x’=’e]] σ m = [(m, x) → E[[e]]σm]
  //   Ts[[a[e1]’=’e2]] σ m = [(m, a::E[[e1]] σ m) → E[[e2]] σ m]
  //   Ts[[x’=’a[e1]]] σ m = [(m, x) → σ(m, a::E[[e1]] σ m)]
  //   Ts[[out’.write(’e’)’]] σ m =
  //     [(σ(m, out), ’data’) → E[[e]]σ m, (σ(m, out), ’valid’) → 1]
  //   Ts[[x’=’in’.read()’]] σ m =
  //     [(m, x) → σ(σ(m, in), ’data’), (σ(m, in), ’ready’) → 0]

  EnvC ts(Stat s, EnvC env, String m) {
    switch(s){
      case Asg a->{return mkEnv(m+","+a.lhs(),ee(a.rhs(),env,m));}
      case AsgMem am->{return mkEnv(mkArrVar(m,am.lhs(),ee(am.idx(), env,m)),ee(am.rhs(),env,m));}
      case ReadMem rm->{return mkEnv(m+","+rm.lhs(),getV(mkArrVar(m,rm.rhs(),ee(rm.idx(),env,m)),env));}
      case WriteCh wc->{int ch=getV(m+","+wc.ch(),env);
        return mkEnv(ch+",data",ee(wc.rhs(), env,m), ch+",valid",1);}
      case ReadCh rc->{int ch=getV(m+","+rc.ch(),env);
        return mkEnv(m+","+rc.lhs(),getV(ch+",data",env),ch+",ready",0);}
      default -> {fail("ts");return null;}
    }
  }
  private String mkArrVar(String m,String v,int idx){
    return m+","+v+"'"+idx;
  }

  //*--------------------------------------------------------------------------
  // Evaluation function for expressions

  // E[[n]] σ m = n
  // E[[v]] σ m = σ(m, v)
  // E[[’Mux(’e1, e2, e3’)’]] σ m =if E[[e1]] σ m = 1 then E[[e2]] σ m then E[[e3]] σ m
  // E[[e1 op e2]] σ m = op(E[[e1]] σ m, E[[e2]] σ m)
  // E[[in’.ready()’]] σ m = σ(σ(m, in), ’ready’) = 1 ∧ σ(σ(m, in), ’valid’) = 0
  // E[[out’.valid()’]]σ m = σ(σ(m, in), ’ready’) = 1 ∧ σ(σ(m, out), ’valid’) = 1

  public int ee(Exp e,EnvC env,String m){
    switch(e){
      case Num n -> {return n.i();}
      case Var v -> {return getV(m+","+v.nm(),env);}
      case Mux mx -> {return ee(mx.e0(),env,m)==1 ? ee(mx.e1(),env,m) : ee(mx.e2(),env,m);}
      case Bin b -> {return binop(b.cmd(),ee(b.e1(),env,m),ee(b.e2(),env,m));}
      case Ready r ->{int ch=getV(m+","+r.s(),env);
           return getV(ch+",ready",env)==1&&getV(ch+",valid",env)==0 ? 1 : 0;}
      case Valid r ->{int ch=getV(m+","+r.s(),env);
           return getV(ch+",ready",env)==1&&getV(ch+",valid",env)==1 ? 1 : 0;}
      default -> {fail("ee");return 0;}
    }
  }

  int binop(String c,int x,int y){
    switch(c){
      case "+"  -> {return x+y; }
      case "-"  -> {return x-y; }
      case "*"  -> {return x*y; }
      case "/"  -> {return y==0?Maxint:x/y; }
      case "%"  -> {return y==0?Maxint:x%y; }
      case ">"  -> {return (x>y?1:0); }
      case ">=" -> {return (x>=y?1:0); }
      case "<"  -> {return (x<y?1:0); }
      case "<=" -> {return (x<=y?1:0); }
      case "==" -> {return (x==y?1:0); }
      case "!=" -> {return (x!=y?1:0); }
      case "|"  -> {return (x==1||y==1?1:0); }
      case "&"  -> {return (x==1&&y==1?1:0); }
      default -> {fail("bin");return 0;}
    }
  }

  //*--------------------------------------------------------------------------
  //   Iterate transistion function from initial state
  //
  // Interpreter [[prg]] = (fix λFλσ.F(T[[prg]]σ ⊕ σ))σ0
  // σ0 = I[[mod+con∗mdcl+]]
  //T[[mod+con∗mdcl+]]σ = (Tm[[mod∗]](Td[[mdcl∗]]) σ) ⊕ R[[con∗]]

  public static void interpreter(Design d,int mx){
    Interpreter ii=new Interpreter(System.out);
    EnvC env0=ii.initEnv(d);
    EnvC iif=ii.iterate(d,env0,mx);
  }
  public static void interpreter(Design d,int mx,String f){
    PrintStream out=outfile(f);
    Interpreter ii=new Interpreter(out);
    EnvC env0=ii.initEnv(d);
    EnvC iif=ii.iterate(d,env0,mx);
    out.close();
  }

  EnvC iterate(Design d,EnvC env0,int mx){
    EnvC env=env0;
    for(int i=0;i<mx;i++) {
      if(showClock)
      out.println("clock at "+i+" "+tos(getLab(env0,getMds(d.decl()))));
      env0=env;
      if(showEnv)
      printEnv(env);
      //printModEnv(d,env0);
      EnvC env1 = tt(d, env);
      env=addEnv(env1,env);
      if(env.equals(env0)){
        System.out.println("end at step "+i);
        out.println("done");break;
      }
    }
    return env;
  }
}


/*--------------------------------------------------------------------------
   Aux1: a collection of helper functions used by the interpreter
*/

class Aux1{
  //--------------------
  // Operations on environments
  public static int getV(String s,EnvC env){
    if(!env.map().containsKey(s))fail("no var "+s+" in"+env);
    return env.map().get(s);}
  public static State getS(int n, ArrayList<State> st){
    for(State s:st)if(s.n()==n)return s;
    return null;
  }
  public static final int Maxint=1000000;
  public static EnvC mkEnv(String s,int i){
    TreeMap<String,Integer> map=new TreeMap<>();
    map.put(s,i);
    return new EnvC(map);
  }
  public static EnvC mkEnv(String s1,int i1,String s2,int i2){
    TreeMap<String,Integer> map=new TreeMap<>();
    map.put(s1,i1);
    map.put(s2,i2);
    return new EnvC(map);
  }
  public static EnvC addEnv(EnvC env1,EnvC env2){
    if(env1==null)return env2;
    if(env2==null)return env1;
    for(String v:env1.map().keySet()){
      env2 =updEnv(v,env1.map().get(v),env2);
    }
    return env2;
  }
  public static EnvC updEnv(String s,int v,EnvC env){
    TreeMap<String,Integer> map =new TreeMap<>();
    map.put(s,v);
    if(env==null)return new EnvC(map);
    for(String t:env.map().keySet()){
      if(!s.equals(t))map.put(t,env.map().get(t));
    }
    return new EnvC(map);
  }

 //-----------------
  // prettyprinter for enviroments
  //
  static void printEnv(EnvC env){
    HashMap<String,ArrayList<Integer>> banks=new HashMap<>();
    TreeMap<String,TreeMap<String,Integer>> map=new TreeMap<>();
    //
    for(String k:env.map().keySet()){
      int v=env.map().get(k);
      String k1=k.substring(0,k.indexOf(",")), k2=k.substring(k.indexOf(",")+1);
      if(!map.containsKey(k1))map.put(k1,new TreeMap<>());
      if(!k2.contains("'")) map.get(k1).put(k2,env.map().get(k));
      else{
        String k3=k1+","+k2.substring(0,k2.indexOf("'"));
        String k4=k2.substring(k2.indexOf("'")+1);
        //if(!map.containsKey(k3))map.put(k3,new TreeMap<>());
        int j=Integer.parseInt(k4);
        if(!banks.containsKey(k3))banks.put(k3,new ArrayList<>());
        while(banks.get(k3).size()<=j)banks.get(k3).add(0);
        banks.get(k3).set(j,v);
      }
    }
    for(String k:map.keySet()){
      TreeMap<String,Integer> m=map.get(k);
      String r=" "+k+" ";
      if(m.containsKey("state"))r+="["+m.get("state")+"] ";
      for(String k1:m.keySet()){
        if(k1.equals("state"))continue;
        r+=k1+"="+m.get(k1)+" ";
      }
      for(String k1:banks.keySet()){
        if(!k1.startsWith(k+","))continue;
        //r+=k1+"="+banks.get(k1)+" ";
        r+=k1.substring(k1.indexOf(",")+1)+"="+banks.get(k1)+" ";
      }
      System.out.println(r);
    }
  }
  //--------------------
  // operations on the abstract syntax

  public static String[] getMds(ArrayList<ValDecl> decl) {
    String[] r=new String[decl.size()];
    for(int i=0;i<r.length;i++)r[i]=decl.get(i).lhs();
    return r;
  }
  public static Module getMod(String rhs, ArrayList<Module> mod) {
    for(Module m:mod)if(rhs.equals(m.nm()))return m;
    return null;
  }
  public static State getState(int n, ArrayList<State> st){
    for(State s:st)if(s.n()==n)return s;
    return null;
  }
  public static int[] getLab(EnvC env,String[] ms){
    int[] r=new int[ms.length];
    for(int i=0;i<r.length;i++) r[i]=getV(ms[i]+",state",env);
    return r;
  }
  //--------------------
  // general java aux functions

  public static String tos(int[] a){return Arrays.toString(a);}


  public static PrintStream outfile(String f){
    try{ return new PrintStream(new FileOutputStream(f));
    }catch(IOException e){
      System.out.println(e);
      return null;
    }
  }
  public static void fail(){throw new RuntimeException("Fail");}
  public static void fail(String s){
    System.out.println("Fail: "+s);
    throw new RuntimeException("Fail "+s);}

  public static final boolean isnumber(String s){
    try{long l= Long.parseLong(s);return true;}
    catch(NumberFormatException e){return false;}
  }

}
