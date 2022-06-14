import java.util.*;

enum Status {
    NOSEARCH, SEARCHING, SEARCHED
}
class Pair
{
    // Return a map entry (key-value pair) from the specified values
    public static <T, U> Map.Entry<T, U> of(T first, U second) {
        return new AbstractMap.SimpleEntry<>(first, second);
    }
}

public class Java_LRParserAnalysis
{
    private static ArrayList<Map.Entry<String,String>> productions;
    private static HashMap<String, HashSet<String>> first;
    private static HashSet<String> endChars;
    private static HashSet<String> nonEndChars;
    private static String start;


    /**
     * status存储查找FOLLOW集合时非终结符的状态
     * 状态NOSEARCH表示还没找过
     * 状态SEARCHING表示正在查找
     * 状态SEARCHED表示已经结束查找
     **/
    private static HashMap<String, Status> status;

    private static ArrayList<Map.Entry<String,Integer>> prog = new ArrayList<>();
    private static HashMap<Map.Entry<Integer,String>,Map.Entry<String,Integer>> actionTable = new HashMap<>();
    private static HashMap<Map.Entry<Integer,String>,Integer> gotoTable = new HashMap<>();
    private static ArrayList<SetOfItems> C = new ArrayList<>();
    private static int statusCnt = 0;
    static class Item{
        //项 [left -> beforeDot · nonTerminal afterNonTerminal, lookAhead]
        private String left;
        private String beforeDot;
        private String afterDot;
        private String lookAhead;

        @Override
        public boolean equals(Object obj) {
            if(this == obj)
                return true;
            if(obj instanceof Item){
                Item item = (Item) obj;
                return this.left.equals(item.left) && this.beforeDot.equals(item.beforeDot) && this.afterDot.equals(item.afterDot) && this.lookAhead.equals(item.lookAhead);
            }
            else
                return false;
        }

        public Item(String left, String beforeDot, String afterDot, String lookAhead) {
            this.left = left;
            this.beforeDot = beforeDot;
            this.afterDot = afterDot;
            this.lookAhead = lookAhead;

        }
    }

    static class SetOfItems{
        public Deque<Item> items;
        public HashMap<String,Integer> GOTO;
        public int statusNum;
        public SetOfItems(Deque<Item> items, int statusNum) {
            this.items = items;
            this.statusNum = statusNum;
            GOTO = new HashMap<>();
        }

        public SetOfItems() {
            this.items = new ArrayDeque<>();
            this.statusNum = 0;
            GOTO = new HashMap<>();
        }

        public void setGOTO(String X, int nextStatus){
            this.GOTO.put(X,nextStatus);
        }

        public void setStatusNum(int statusNum) {
            this.statusNum = statusNum;
        }

        @Override
        public boolean equals(Object obj) {
            if(this == obj)
                return true;
            if(obj instanceof SetOfItems){
                //互相包含item,则相等,否者不相等
                for(Item item:this.items){
                    if(!((SetOfItems) obj).items.contains(item))
                        return false;
                }
                for(Item item: ((SetOfItems) obj).items){
                    if(!this.items.contains(item))
                        return false;
                }
                return true;
            }
            else
                return false;
        }

        private void addItem(Item item){
            if(!this.items.contains(item))
                this.items.add(item);
        }
    }

    static SetOfItems CLOSURE(SetOfItems I){
        int lastItemNum = I.items.size() -1;
        while (lastItemNum != I.items.size()){
            lastItemNum = I.items.size();
            Deque<Item> tmpItems = ((ArrayDeque<Item>) I.items).clone();
            for(Item item:tmpItems){
                String[] afterDotSubs = item.afterDot.trim().split(" ");
                String nonTerminal = nonEndChars.contains(afterDotSubs[0])?afterDotSubs[0] :"";
                if(nonTerminal != ""){
                    //遍历G'中item.nonTerminal -> rights
                    for(Map.Entry<String,String> production:productions){
                        if(production.getKey().equals(nonTerminal)){
                            String right = production.getValue();
                            //遍历FIRST(afterNonTerminal lookAhead)中的每一个终结符terminal
                            String afterNonTerminal = "";
                            for(int i=1;i< afterDotSubs.length;i++){
                                afterNonTerminal = afterNonTerminal + " " + afterDotSubs[i];
                            }
                            HashSet<String> first = get_rightItems_first(afterNonTerminal+" "+item.lookAhead);
                            String left = nonTerminal;
                            String beforeDot = "";
                            String afterDot = right;
                            for(String terminal:first){
                                I.addItem(new Item(left,beforeDot,afterDot,terminal));
                            }
                        }

                    }
                }
            }
        }

        return I;
    }

    static SetOfItems GOTO(SetOfItems I, String nonTerminal){
        SetOfItems J = new SetOfItems();
        for(Item item:I.items){
            String[] afterDotSubs = item.afterDot.trim().split(" ");
            if(afterDotSubs[0].equals(nonTerminal)){
                String left0 = item.left;
                String beforeDot0 = "";
                String afterDot0 = "";
                String lookAhead0 = item.lookAhead;
                if(afterDotSubs.length>0){
                    String nextChar = afterDotSubs[0];
                    beforeDot0 = (item.beforeDot+" "+nextChar).trim();
                    for(int i=1;i< afterDotSubs.length;i++){
                        afterDot0 = afterDot0+" "+afterDotSubs[i];
                    }
                    afterDot0 = afterDot0.trim();
                }
                Item newItem = new Item(left0,beforeDot0,afterDot0,lookAhead0);
                J.addItem(newItem);

            }

        }
        return CLOSURE(J);
    }

    private static void initIterms(){
        SetOfItems initStatus = new SetOfItems();
        initStatus.addItem(new Item("program'","","program","$"));
        initStatus = CLOSURE(initStatus);
        initStatus.setStatusNum(statusCnt++);

        C.add(initStatus);
        int lastItemNum = C.size()-1;
        while(lastItemNum != C.size()){
            lastItemNum = C.size();
            ArrayList<SetOfItems> tmpC = (ArrayList<SetOfItems>) C.clone();
            for(SetOfItems I:tmpC){
                //遍历每个文法符号，包括终结符和非终结符
                for(String X:endChars){
                    if(X.equals("E"))
                        continue;
                    SetOfItems NextI = GOTO(I,X);
                    if(C.contains(NextI)){
                        int nextStatus = 0;
                        for(SetOfItems item:C){
                            if(item.equals(NextI)){
                                nextStatus = item.statusNum;
                                break;
                            }
                        }
                        C.get(I.statusNum).setGOTO(X,nextStatus);
                    }
                    else if(NextI.items.size() != 0){
                        NextI.setStatusNum(statusCnt++);
                        C.get(I.statusNum).setGOTO(X,statusCnt-1);
                        C.add(NextI);
                    }
                }
                for(String X:nonEndChars){
                    SetOfItems NextI = GOTO(I,X);
                    if(C.contains(NextI)){
                        int nextStatus = 0;
                        for(SetOfItems item:C){
                            if(item.equals(NextI)){
                                nextStatus = item.statusNum;
                                break;
                            }
                        }
                        C.get(I.statusNum).setGOTO(X,nextStatus);
                    }
                    else if(NextI.items.size() != 0){
                        NextI.setStatusNum(statusCnt++);
                        C.get(I.statusNum).setGOTO(X,statusCnt-1);
                        C.add(NextI);
                    }
                }
            }
        }
        for(SetOfItems closure:C){
            System.out.print(closure.statusNum+" ");

            closure.GOTO.forEach((key,value)->{
                System.out.print(key+"->"+value+" ");
            });
            System.out.print(" ");
            System.out.print(closure.items.size()+"个 ");
            for(Item item:closure.items){
                System.out.print("["+item.left+" -> "+item.beforeDot+"."+item.afterDot+", "+item.lookAhead+"]; ");
            }
            System.out.println();
        }
        System.out.println(C.size());
    }
    private static void init_data() {

        //init production
        productions = new ArrayList<>();
        productions.add(Pair.of("program'","program"));
        productions.add(Pair.of("program","compoundstmt"));
        productions.add(Pair.of("stmt","ifstmt"));
        productions.add(Pair.of("stmt","whilestmt"));
        productions.add(Pair.of("stmt","assgstmt"));
        productions.add(Pair.of("stmt","compoundstmt"));
        productions.add(Pair.of("compoundstmt","{ stmts }"));
        productions.add(Pair.of("stmts","stmt stmts"));
        productions.add(Pair.of("stmts","E"));
        productions.add(Pair.of("ifstmt","if ( boolexpr ) then stmt else stmt"));
        productions.add(Pair.of("whilestmt","while ( boolexpr ) stmt"));
        productions.add(Pair.of("assgstmt","ID = arithexpr ;"));
        productions.add(Pair.of("boolexpr","arithexpr boolop arithexpr"));
        productions.add(Pair.of("boolop","<"));
        productions.add(Pair.of("boolop",">"));
        productions.add(Pair.of("boolop","<="));
        productions.add(Pair.of("boolop",">="));
        productions.add(Pair.of("boolop","=="));
        productions.add(Pair.of("arithexpr","multexpr arithexprprime"));
        productions.add(Pair.of("arithexprprime","+ multexpr arithexprprime"));
        productions.add(Pair.of("arithexprprime","- multexpr arithexprprime"));
        productions.add(Pair.of("arithexprprime","E"));
        productions.add(Pair.of("multexpr","simpleexpr multexprprime"));
        productions.add(Pair.of("multexprprime","* simpleexpr multexprprime"));
        productions.add(Pair.of("multexprprime","/ simpleexpr multexprprime"));
        productions.add(Pair.of("multexprprime","E"));
        productions.add(Pair.of("simpleexpr","ID"));
        productions.add(Pair.of("simpleexpr","NUM"));
        productions.add(Pair.of("simpleexpr","( arithexpr )"));


        //init start 增广之前的start
        start = "program";

        //init terminal
        endChars = new HashSet<>();
        endChars.add("{");
        endChars.add("}");
        endChars.add("if");
        endChars.add("(");
        endChars.add(")");
        endChars.add("then");
        endChars.add("else");
        endChars.add("while");
        endChars.add("ID");
        endChars.add("=");
        endChars.add(">");
        endChars.add("<");
        endChars.add(">=");
        endChars.add("<=");
        endChars.add("==");
        endChars.add("+");
        endChars.add("-");
        endChars.add("*");
        endChars.add("/");
        endChars.add("NUM");
        endChars.add("E");
        endChars.add(";");


        //init nonterminal
        nonEndChars = new HashSet<>();
        nonEndChars.add("program");
        nonEndChars.add("stmt");
        nonEndChars.add("compoundstmt");
        nonEndChars.add("stmts");
        nonEndChars.add("ifstmt");
        nonEndChars.add("whilestmt");
        nonEndChars.add("assgstmt");
        nonEndChars.add("boolexpr");
        nonEndChars.add("boolop");
        nonEndChars.add("arithexpr");
        nonEndChars.add("arithexprprime");
        nonEndChars.add("multexpr");
        nonEndChars.add("multexprprime");
        nonEndChars.add("simpleexpr");

        //init first
        first = new HashMap<>();
        getFirst();

        //init items
        initIterms();

        //get table
        getTable();

        System.out.println(actionTable.toString()+ gotoTable.toString());
    }

    private static void getTable(){
        for(SetOfItems items:C){
            for(Item item:items.items){
                if(item.afterDot.equals("")){
                    //接受 accept
                    if(item.beforeDot.equals(start)){
                        actionTable.put(Pair.of(items.statusNum, item.lookAhead),Pair.of("acc",0));
                    }
                    //规约 reduction
                    else{
                        int productionNum = 0;
                        for(int i=0;i<productions.size();i++){
                            if(productions.get(i).getKey().equals(item.left) && productions.get(i).getValue().equals(item.beforeDot)){
                                productionNum = i;
                                break;
                            }
                        }
                        actionTable.put(Pair.of(items.statusNum, item.lookAhead),Pair.of("r",productionNum));
                    }
                }
                else{
                    String[] afterDotSubs = item.afterDot.trim().split(" ");
                    if(endChars.contains(afterDotSubs[0]) && items.GOTO.get(afterDotSubs[0]) != null){
                        int nextStatus = items.GOTO.get(afterDotSubs[0]);
                        actionTable.put(Pair.of(items.statusNum, afterDotSubs[0]),Pair.of("s",nextStatus));
                    }
                }

            }
        }
    }

    private static HashSet<String> firstx(String x) {
        HashSet<String> first = new HashSet<>();

        //x是终结符，其中E也在终结符里面
        if (endChars.contains(x)) {
            first.add(x);
            return first;
        } else {
            //右部各符号FIRST集相加
            for (Map.Entry<String,String> production:productions) {
                if(production.getKey().equals(x)){
                    String rightItem = production.getValue();
                    String[] rightItemString = rightItem.split(" ");
                    if (rightItemString.length == 1) {
                        first.addAll(firstx(rightItemString[0]));
                    } else {
                        for (int i = 0; i < rightItemString.length; i++) {
                            String rightItemSub = rightItemString[i];
                            if (endChars.contains(rightItemSub)) {
                                first.add(rightItemSub);
                                break;
                            } else {
                                HashSet<String> rightItemFirst = firstx(rightItemSub);
                                //包含空
                                if (rightItemFirst.contains("E")) {
                                    //rightItem是最后一个符号，把空加入FIRST集
                                    if (i == rightItemString.length - 1) {
                                        first.addAll(rightItemFirst);
                                    } else {
                                        rightItemFirst.remove("E");
                                        first.addAll(rightItemFirst);
                                    }
                                }
                                //不包含空
                                else {
                                    first.addAll(rightItemFirst);
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }
        return first;
    }

    private static void getFirst() {
        //init first
        //终结符的FIRST集就是本身
        for (String endChar : endChars) {
            HashSet<String> tmp = new HashSet<>();
            tmp.add(endChar);
            first.put(endChar, tmp);
        }
        //添加"$"
        HashSet<String> dollar = new HashSet<>();
        dollar.add("$");
        first.put("$",dollar);

        //遍历非终结符
        for (String nonEndChar : nonEndChars) {
            first.put(nonEndChar, firstx(nonEndChar));
        }
    }

    private static HashSet<String> get_rightItems_first(String rightItem) {
        rightItem = rightItem.trim();
        String[] rightItemChars = rightItem.split(" ");
        // A -> Y1Y2...Yn
        HashSet<String> res = new HashSet<>();
        boolean flag = true;
        for (String rightItemChar : rightItemChars) {
            HashSet<String> firstOfChar = first.get(rightItemChar);
            //Y1有空
            if (firstOfChar.contains("E")) {
                res.addAll(firstOfChar);
                res.remove("E");
            }
            //Y1无空
            else {
                res.addAll(firstOfChar);
                flag = false;
                break;
            }
        }
        if (flag) {
            res.add("E");
        }
        return res;
    }

    /**
     *  this method is to read the standard input
     */
    private static void read_prog()
    {
        Scanner sc = new Scanner(System.in);
        Integer lineNum = 1;
        while (sc.hasNextLine()) {
            String line = sc.nextLine();
            String[] tmp = line.split(" ");
            for(String Char:tmp){
                if(Char.equals(""))
                    continue;
                prog.add(Pair.of(Char,lineNum));
            }
            lineNum ++;
        }
    }


    // add your method here!!



    /**
     *  you should add some code in this method to achieve this lab
     */
    private static void analysis()
    {

    }

    /**
     * this is the main method
     * @param args
     */
    public static void main(String[] args) {
        read_prog();
        init_data();
        analysis();
    }
}
