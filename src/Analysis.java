import java.util.*;
public class Analysis extends AnalysisAux {
  public static void main(String[] args) {
  }
  Interpreter interpreter=new Interpreter(System.out);
  /*
  The abstract environment is
  σ˜ ∈ Σ˜ : (Reg_rv ∪ Reg_s) → (℘(2) ∪ N)
  In the implementation it is EnvC : String -> Integer
  As domain ℘(2) we use the numbers {0,1,2} with 0 as {0}, 1 as {1} and 2 as {0,1}
  The empty set correspond to mapping of a string to an integer in the partial map
  */

  //---------------------------------
  //
  // α : Σ→ ˜Σ
  // α(σ) = λx. if x ∈ Regrv then {σ(x)} else if x ∈ Regs then σ(x) else⊥
  // θ0 = α( [[mod+con∗mdcl+]])

  static EnvC alpha(EnvC env) {
    if(env==null) return env;
    TreeMap<String, Integer> map = new TreeMap<>();
    for (String s : env.map().keySet()) {
      if (isRegrv(s)||isRegst(s)) map.put(s, env.map().get(s));
    }
    return new EnvC(map);
  }

  EnvC theta0(Design d){return alpha(interpreter.initEnv(d));}

  //---------------------------------
  //
  HashSet<EnvC> iterate(Design d) {
    PrettyPrint.prettyprint(d);
    EnvC env0 = theta0(d);
    HashSet<EnvC> envs = new HashSet<>();
    envs.add(env0);

    for (int i = 0; i < 40; i++) {
      System.out.println("Step " + (i+1));
      HashSet<EnvC> envs1 = new HashSet<>();
      for (EnvC env : envs) {
        List<EnvC> envcs2 = tt(d, env);
        envs1.addAll(envcs2);
      }
      if(envs.containsAll(envs1)) {  System.out.println("Done");break;}
      envs.addAll(envs1);
    }
    return envs;
  }

  //---------------------------------
  //

  // T˜ [[m1 · · ·mn]] ℓ σ˜ = Tt [[Mod1]]σ˜m1⊗· · ·⊗Tt [[Modn]]σ˜mn

  List<EnvC> tt(Design d, EnvC env) {
    List<List<EnvC>> envss = new ArrayList<>();
    for (ValDecl v : d.decl())
      envss.add(td(v.lhs(), v.rhs(), d.mod(), env));
    //envss.forEach(s -> System.out.println("> " + s));
    List<EnvC> envs = allCombi(0, envss);
    EnvC envr = rr(env);
    for (int i = 0; i < envs.size(); i++) {
      envs.set(i, addEnv(addEnv(envr, envs.get(i)), env));
    }
    return envs;
  }
  List<EnvC> td(String lhs, String rhs, ArrayList<Module> mod, EnvC env) {
    Module mm = getMod(rhs, mod);
    return td(mm, env, lhs);
  }

  List<EnvC> allCombi(int i, List<List<EnvC>> envss) {
    if (i == envss.size() - 1) return envss.get(i);
    if (i > envss.size() - 1) return new ArrayList<EnvC>();
    List<EnvC> envs1 = allCombi(i + 1, envss);
    List<EnvC> envs2 = envss.get(i);
    List<EnvC> ret = new ArrayList<>();
    for (EnvC env1 : envs1)
      for (EnvC env2 : envs2)
        ret.add(addEnv(env1, env2));
    return ret;
  }

  //---------------------------------
  // R˜ [[con1 · · ·conn]] σ˜ = R˜ [[con1]] σ˜ ⊕· · ·⊕R˜ [[conn]] σ˜
  // R˜ [[m1.out1'<>'m2.in2]] σ˜ = let c = σ˜ (m1,out1)
  //    if σ˜ (c,'ready') = {0,1} then [(c,'ready') → {1}, (c,'valid') →{0} ∪ σ˜(c,'valid')]
  //    else if σ˜ (c,'ready') = {0} then [(c,'ready') → {1}, (c,'valid') →{0}] else ⊥Σ

  EnvC rr(EnvC env) { // changes to environment
    EnvC env1 = mkEnv();
    for (String v : env.map().keySet()) {
      if (!v.endsWith(",ready")) continue;
      String ch = v.substring(0, v.indexOf(","));
      String r1 = ch + ",ready", r2 = ch + ",valid";
      int rd = getV(r1, env), vl = getV(r2, env);
      if (rd == 0) env1 = addEnv(mkEnv(r1, 1, r2, 0), env1);
      if (rd == 2) env1 = addEnv(mkEnv(r1, 1, r2, lubB(0, vl)), env1);
    }
    return env1;
  }

  //---------------------------------
  // T˜ [[state1 · · · staten]] σ˜ m = T˜ [[state1]]σ˜ m ⊕· · ·⊕ T˜ [[staten]]σ˜ m
  // T˜ [['state 'n' when'e s1 · · · sn 'goto'eg]] σ˜ m =
  //    if σ(m,'state') ̸= n then Σ⊥ else
  //    if E˜ [[e]] σ˜ m ̸= 1 then Σ⊥ else
  // T˜ [[s1]]σ˜ m ⊕· · ·⊕ T˜[[sn]] σ m ⊕[(m,'state'  → E˜ [[eg]] σ m]

  List<EnvC> td(Module mod, EnvC env, String m) {
    ArrayList<State> sts=mod.states();
    int sn = Aux1.getV(m + ",state", env);
    State s = getState(sn, sts);
    return tt(s, env, m);
  }

  List<EnvC> tt(State s, EnvC env, String m) {
    List<EnvC> envs = new ArrayList<>();
    int v = ee(s.cmd(), env, m);
    if (v == 0 || v == 2) envs.add(null);
    if (v == 0) return envs;
    List<Integer> nxt = new ArrayList<>();
    Eg(s.g(), nxt);
    EnvC envst = ss(s.stm(), env, m);
    for (int i : nxt) envs.add(addEnv(envst, mkEnv(m + ",state", i)));
    return envs;
  }

  //---------------------------------
  // ˜Eg[[g]] :℘(N)
  // ˜Eg[[n]] = {n}
  // ˜Eg[['Mux('e1,e2,e3')']] = ˜Ege1 ∪ ˜Ege2

  void Eg(Goto g, List<Integer> nxt) {
    switch (g) {
      case Next n -> nxt.add(n.i());
      case Cond c -> {
        Eg(c.g1(), nxt);
        Eg(c.g2(), nxt);
      }
      default -> throw new RuntimeException("Unreachable");
    }
  }

  //---------------------------------
  // T˜ s[[s]] Σ˜ → A → Σ˜
  // T˜ s[[out'.write('e')']] σ˜ m = [(σ(m,out),'valid')  →{1}]
  // T˜ s[[x'='in'.read()']] σ˜ m = [(σ(m, in),'ready')  →{0}]

  EnvC ss(List<Stat> ss, EnvC env, String m) {
    EnvC ret = mkEnv();
    for (Stat stat : ss) {
      switch (stat) {
        case ReadCh ch1 -> {
          int ch = getV(m + "," + ch1.ch(), env);
          ret=addEnv(mkEnv(ch + ",ready",0),ret);
        }
        case WriteCh ch1 -> {
          int ch = getV(m + "," + ch1.ch(), env);
          ret=addEnv(mkEnv(ch + ",valid",1),ret);
        }
        default -> {}
      }
    }
    return ret;
  }

  //---------------------------------
  //  E˜[[e]] : ˜Σ→A→℘(2)
  //  E˜ [[in'.ready()']] σ˜ m = {1 | 1 ∈ σ(σ(m, in),'ready')∧0 ∈ σ(σ(m, in),'valid')}∪
  //          {0 | 1 ̸∈ σ(σ(m, in),'ready')∨0 ̸∈ σ(σ(m, in),'valid')}
  //  E˜ [[in'.valid()']]σ˜ m = {1 | 1 ∈ σ(σ(m, in),'ready')∧1 ∈ σ(σ(m, in),'valid')}∪
  //          {0 | 1 ̸∈ σ(σ(m, in),'ready')∨1 ̸∈ σ(σ(m, in),'valid')}

  int ee(Exp e, EnvC env, String m) {
    switch (e) {
      case Num n -> {
        return 1;
      }
      case Ready r -> {
        int ch = getV(m + "," + r.s(), env);
        int rd = getV(ch + ",ready", env);
        int vl = getV(ch + ",valid", env);
        if (rd == 1 && vl == 0) return 1; //is true
        if (rd == 0 || vl == 1) return 0; //cannot be true
        return 2;
      }
      case Valid r -> {
        int ch = getV(m + "," + r.s(), env);
        int rd = getV(ch + ",ready", env);
        int vl = getV(ch + ",valid", env);
        if (rd == 1 && vl == 1) return 1; // is true
        if (rd == 0 || vl == 0) return 0; // cannot be true
        return 2;
      }
      default -> {
        fail("ee");
        return 0;
      }
    }
  }
}

//--------------------------------------------------

class AnalysisAux {
  // Aux functions

  // lub operation for 0-1 values. 2 represent {0,1}
  public static int lubB(int a, int b) {
    if(a==b) return a; return 2;
  }

  static String env2lab(EnvC env) {
    String labv="";
    if(env==null) return " ";
    for(String v: env.map().keySet()) {
      if(v.contains(",state"))labv+=" "+env.map().get(v);
    }
    return labv;
  }

  static EnvC lubEnv(EnvC env1, EnvC env2) {
    if(env1==null) return env2;
    if(env2==null) return env1;
    TreeMap<String,Integer> map=new TreeMap<>();
    TreeSet<String> keys=new TreeSet<>();
    keys.addAll(env1.map().keySet());
    keys.addAll(env1.map().keySet());
    for(String k: keys) {
      Integer v1=env1.map().get(k), v2=env2.map().get(k);
      if(v1==null)map.put(k,v2); else
      if(v2==null)map.put(k,v1); else map.put(k,lubB(v1,v2));
    }
    return new EnvC(map);
  }
  static boolean isRegrv(String s){ // is ready valid registers
    return s.contains(",ready") || s.contains(",valid");
  }
  static boolean isRegst(String s){ // is state chnnel registers
    return s.contains(",in") || s.contains(",out")|| s.contains(",state");
  }
  static boolean isRegch(String s){ // is state chnnel registers
    return s.contains(",in") || s.contains(",out");
  }

  public static EnvC mkEnv(){
    TreeMap<String,Integer> map=new TreeMap<>();
    return new EnvC(map);
  }
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


  public static int getV(String s,EnvC env){
    if(!env.map().containsKey(s))fail("no var "+s+" in"+env);
    return env.map().get(s);
  }
  public static void fail(String s){
    System.out.println("Fail: "+s);
    throw new RuntimeException("Fail "+s);
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
  public static EnvC addEnv(EnvC env1,EnvC env2){
    if(env1==null)return env2;
    if(env2==null)return env1;
    for(String v:env1.map().keySet()){
      env2 =updEnv(v,env1.map().get(v),env2);
    }
    return env2;
  }

  static void showEnvs(HashSet<EnvC> envs){
    if(envs.size()==0)return;
    List<String> svar =envs.iterator().next().map().keySet().stream().filter(s-> s.contains(",state")).toList();
    System.out.println(svar);
    for(String sv: svar){
      List<Integer> st=envs.stream().map(ev-> ev.map().get(sv)).distinct().sorted().toList();
      for(Integer i: st){
        System.out.println(sv+" "+i);
        for(EnvC ev: envs){
          if(getV(sv,ev)!=i)continue;
          String r="";
          for(String k: ev.map().keySet()){
            if(k.equals(sv)||isRegch(k))continue;
            r+="  "+k+": "+ev.map().get(k);
          }
          System.out.println(r);
        }
      }
    }
  }

  public static Module getMod(String rhs, ArrayList<Module> mod) {
    for(Module m:mod)if(rhs.equals(m.nm()))return m;
    return null;
  }
  public static State getState(int n, ArrayList<State> st){
    for(State s:st)if(s.n()==n)return s;
    return null;
  }
}

