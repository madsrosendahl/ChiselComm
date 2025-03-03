import java.lang.reflect.AnnotatedType;
import java.lang.reflect.Constructor;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

record Node(String h, List<Node> lst){
  public String toString(){return h+(lst==null||lst.size()==0?"":lst);}
  Node get(int i){return lst==null?null:lst.get(i);}
  int size(){return lst==null?0:lst.size();}
  Stream<Node> stream(){return (lst==null?new ArrayList<Node>():lst).stream();}
}

// The Node record is used, primarily, for tree structures. A Node record contains a tag a list
// of nodes as children. A leaf is a node without children.
//
// The node record can also be used to represent a list of nodes. We will use the tags "list"
// and "empty" to denote lists. Unlike Lisp the elements of the list are the first level
// children of the node.
//
// The Nodes class contain helper functions to construct and process Node objects


public class Nodes {
  public static void main(String[] args) {
  }

  //-----------------------------------------------------------
  public static Node node(String lhs,Node ... lst){
    ArrayList<Node> rhs=new ArrayList<>();
    for(Node x:lst)rhs.add(x);
    return new Node(lhs,rhs);

  }

  //-----------------------------------------------------------
  //
  // Translate a Node structure to a record assuming that tags a names for records
  // It will call the canonical constructor for the named record and with children
  // converted into records recursively.
  // Lists are converted into lists of records, Strings and integers are converted
  //
  public static Object mkRecord(Node n){
    return mkRecord(n.h(),n);
  }
  private static Object mkRecord(String tp,Node n){
    if(n==null||tp==null)return null;
    if(tp.equals("String"))
      return mkString(n);
    if(tp.equals("int")||tp.equals("Integer"))
      return mkInteger(n);
    if(tp.startsWith("List<")||tp.startsWith("java.util.ArrayList<"))
      return mkList(tp,n);
    if(n.h().equals("list")||n.h().equals("empty")){
      System.out.println("problem found list "+tp+" "+n);
      return null;
    }
    String h=n.h();
    List<Node> lhs=n.lst();
    //System.out.println("mk "+tp+" "+c+" "+n);
    if(tp.equals(h)||tp.equals(getInterface(h))){}else{
      System.out.println("problem "+tp+" "+h+" "+n);
      System.out.println(suggestRecord(n));
      return null;
    }
    List<String> argtp=getArgTypes(h);
    if(argtp==null||argtp.size()!= lhs.size()){
      System.out.println("problem "+argtp+" "+n);
      System.out.println(suggestRecord(n));
      return null;
    }
    Class c=null;
    try{c=Class.forName(n.h());}catch(ClassNotFoundException e){}
    List<Object> args=new ArrayList<>();
    Constructor<?> cn = getCanonicalConstructor(c);
    if(c==null||cn==null){
      System.out.println("mo constructor "+h+" "+argtp+" "+n);
      System.out.println(suggestRecord(n));
      return null;
    }
    for(int i=0;i<lhs.size();i++)
      args.add(mkRecord(argtp.get(i), lhs.get(i)));
    Object r1=null;
    try { r1 = cn.newInstance(args.toArray());}catch(Exception e){}
    return r1;
  }

  private static Object mkInteger(Node n) {
    return (Integer) (Integer.parseInt(n.h()));
  }

  private static Object mkString(Node n) {
    return n.h();
  }

  private static Object mkList(String tp,Node n) {
    //System.out.println("mkList "+tp+" "+n);
    if(!tp.contains("<")||!tp.contains(">")){
      System.out.println("problem "+tp+" "+n);
      return null;
    }
    String t1=tp.substring(tp.indexOf("<")+1);
    t1=t1.substring(0,t1.indexOf(">"));
    List<Node> lhs=n.lst();
    List<Object> res=new ArrayList<Object>();
    for(Node n1:lhs)res.add(mkRecord(t1,n1));
    return res;
  }

  private static String getInterface(String name) {
    try {
      Class c = Class.forName(name);
      AnnotatedType[] a=c.getAnnotatedInterfaces();
      //System.out.println(Arrays.toString(a));
      //System.out.println(c);
      if(a.length==1)return cleanType(a[0].toString());
    }catch (ClassNotFoundException e){
      System.out.println("No constructor for "+name);
    }
    return "";
  }

  private static List<String> getArgTypes(String par){
    ArrayList<String> res=new ArrayList<>();
    try {
      Class c = Class.forName(par);
      //System.out.println("Class "+c);
      RecordComponent[] cr= c.getRecordComponents();
      //System.out.println("cr "+Arrays.toString(cr));
      for(int i=0;i<cr.length;i++){
        String t=cr[i].getGenericType().toString();
        t=cleanType(t);
        //System.out.println("type "+t);
        res.add(t);
      }
      return res;
    }catch (ClassNotFoundException e){
      System.out.println("No constructor for "+par);
      return null;
    }
  }
  private static String cleanType(String t){
    t=replaceStr(t,"class ","");
    t=replaceStr(t,"interface ","");
    t=replaceStr(t,"java.lang.String","String");
    t=replaceStr(t,"java.lang.Integer","Integer");
    t=replaceStr(t,"java.util.List","List");
    return t;
  }
  private static String replaceStr(String t,String str,String replace){
    int i=t.indexOf(str);
    if(i<0)return t;
    t=t.substring(0,i)+replace+t.substring(i+str.length());
    return t;
  }
  private static <T extends Record> Constructor<T> getCanonicalConstructor(Class<T> cls){
    try {
      RecordComponent[] cr = cls.getRecordComponents();
      Class<?>[] paramTypes =new Class<?>[cr.length];
      for(int i=0;i<cr.length;i++) paramTypes[i]=cr[i].getType();
      return cls.getDeclaredConstructor(paramTypes);
    }catch(Exception e){
      System.out.println("No constructor for "+cls);
      return null;
    }
  }
  private static String suggestRecord(Node n) {
    String r="record "+n.h()+"(";
    List<Node> lst=n.lst();
    for(int i=0;i<lst.size();i++){
      if(i>0)r+=", ";
      Node n1=lst.get(i);
      if(n1.h().equals("list")){
        r+="List<>";
      }else r+=lst.get(i).h();
      r+=" a"+i;
    }
    r+="){}";
    return r;
  }
  //------------------------
  //
  // pretty printer for nodes

  void printNode(Node n) { printNode(0,n); System.out.println();}
  void printNode(int i, Node n) {
    for(int j=0;j<i;j++)System.out.print(" ");
    if(n==null){ System.out.print("null");return;}
    if(isSimple2(n)) System.out.print(n.toString());
    else{
      int j0=0;
      if(n.lst()==null){ System.out.print(n.h());return;}
      System.out.print(n.h()+"[");
      List<Node> rhs=n.lst(); int sz= rhs.size();
      if(sz>1&&isSimple2(rhs.get(j0))){
        System.out.print(rhs.get(j0)); j0++;
        System.out.println(",");
      } else
        System.out.println();
      for(int j=j0;j<sz;j++ ){
        printNode(i+2,rhs.get(j));
        if(j<sz-1) System.out.println(",");
      }
      System.out.print("]");
    }
  }
  boolean isAtom(Node n) {return n==null||n.lst()==null||n.lst().isEmpty();}
  boolean isSimple(Node n){return isAtom(n)||n.lst().stream().allMatch(t->isAtom(t));}
  boolean isSimple2(Node n){return isSimple(n)||n.lst().stream().allMatch(t->isSimple(t));}

  //-------------------------------
  // general list operations
  boolean isList(Node n) {
    return n.h().equals("empty")||n.h().equals("list");
  }
  boolean nullp(Node n) {
    return n==null||(n.h().equals("empty")||n.h().equals("list"))&&(length(n)==0);
  }
  boolean atomp(Node n) {
    return length(n)==0;
  }
  int length(Node n) {
    if(n==null||n.lst()==null)return 0;
    return n.lst().size();
  }
  Node head(Node n) {
    return n.lst().get(0);
  }
  Node tail(Node n) {
    if(n==null||n.lst()==null)return node("empty");
    ArrayList<Node> lst1=new ArrayList<>();
    for(int i=1;i<n.lst().size();i++)lst1.add(n.lst().get(i));
    return new Node(n.h(),lst1);
  }
  Node cons(Node n1,Node n2) {
    if(nullp(n2))return node("list",n1);
    ArrayList<Node> lst1=new ArrayList<>();
    lst1.add(n1); lst1.addAll(n2.lst());
    return new Node("list",lst1);
  }
  Node flatList(Node n1) {
    if(nullp(n1))return node("empty");
    if(!n1.h().equals("list"))return n1;
    return flatList(n1.lst());
  }
  Node flatList(List<Node> lst) {
    if(lst==null||lst.size()==0)return node("empty");
    ArrayList<Node> lst1=new ArrayList<>();
    //System.out.println("FL "+lst);
    for(Node n2:lst) {
      Node n3=flatList(n2);
      if (nullp(n3)) continue;
      if(!isList(n3))lst1.add(n3);
      else lst1.addAll(n3.lst());
    }
    if(lst1.size()==0)return node("empty");
    //System.out.println("fl "+lst);
    return new Node("list",lst1);
  }


  //---------------------------------

  void fail(Object n){System.out.println("Fail "+n);fail();}
  void fail(){throw new RuntimeException("Fail");}

}
