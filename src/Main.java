import java.util.HashSet;

public class Main {
  public static void main(String[] args) {
    Design d= Parser.parseDesign("in\\prog8.txt");
    //System.out.println(d);
    PrettyPrint.prettyprint(d);
    Chisel.toChisel(d,"Main8");

    Analysis a = new Analysis();
    HashSet<EnvC> envs=a.iterate(d);
    AnalysisAux.showEnvs(envs);


  }
}