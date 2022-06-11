import java.util.*;

public class Java_LRParserAnalysis
{
    private static HashMap<String, String[]> rule;
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
        private static Deque<Item> items;
        private static int statusNum;
        private static HashMap<String,Integer> GOTO;

        public SetOfItems(Deque<Item> items, int statusNum) {
            this.items = items;
            this.statusNum = statusNum;
            this.GOTO = new HashMap<>();
        }

        public SetOfItems() {
            this.items = new ArrayDeque<>();
            this.statusNum = 0;
            this.GOTO = new HashMap<>();
        }

        public void setStatusNum(int statusNum) {
            this.statusNum = statusNum;
        }

        public void setGOTO(String X, int nextStatus){
            this.GOTO.put(X,nextStatus);
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
                    for(String right:rule.get(nonTerminal)){
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
                    beforeDot0 = item.beforeDot+" "+nextChar;
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
        ArrayList<SetOfItems> C = new ArrayList<>();

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
                    if(NextI.items.size() != 0 && !C.contains(NextI)){
                        NextI.setStatusNum(statusCnt++);
                        I.setGOTO(X,statusCnt-1);
                        C.add(NextI);
                    }
                }
                for(String X:nonEndChars){
                    SetOfItems NextI = GOTO(I,X);
                    if(NextI.items.size() != 0 && !C.contains(NextI)){
                        NextI.setStatusNum(statusCnt++);
                        I.setGOTO(X,statusCnt-1);
                        C.add(NextI);
                    }
                }
            }
        }
        for(SetOfItems closure:C){
            System.out.print(closure.statusNum+" ");
            System.out.print(closure.items.size()+"个 ");
            for(Item item:closure.items){
                System.out.print("["+item.left+" -> "+item.beforeDot+"."+item.afterDot+", "+item.lookAhead+"]; ");
            }
            System.out.println();
        }
        System.out.println(C.size());
    }
    private static void init_data() {

        //init rule
        rule = new HashMap<>();
        rule.put("program'",new String[]{"program"});
        rule.put("program", new String[]{"compoundstmt"});
        rule.put("stmt", new String[]{"ifstmt", "whilestmt", "assgstmt", "compoundstmt"});
        rule.put("compoundstmt", new String[]{"{ stmts }"});
        rule.put("stmts", new String[]{"stmt stmts", "E"});
        rule.put("ifstmt", new String[]{"if ( boolexpr ) then stmt else stmt"});
        rule.put("whilestmt", new String[]{"while ( boolexpr ) stmt"});
        rule.put("assgstmt", new String[]{"ID = arithexpr ;"});
        rule.put("boolexpr", new String[]{"arithexpr boolop arithexpr"});
        rule.put("boolop", new String[]{"<", ">", "<=", ">=", "=="});
        rule.put("arithexpr", new String[]{"multexpr arithexprprime"});
        rule.put("arithexprprime", new String[]{"+ multexpr arithexprprime", "- multexpr arithexprprime", "E"});
        rule.put("multexpr", new String[]{"simpleexpr multexprprime"});
        rule.put("multexprprime", new String[]{"* simpleexpr multexprprime", "/ simpleexpr multexprprime", "E"});
        rule.put("simpleexpr", new String[]{"ID", "NUM", "( arithexpr )"});

        //init start
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
        get_first();

    }

    private static HashSet<String> FIRSTx(String x) {
        HashSet<String> first = new HashSet<>();

        //x是终结符，其中E也在终结符里面
        if (endChars.contains(x)) {
            first.add(x);
            return first;
        } else {
            //右部各符号FIRST集相加
            String[] rightItems = rule.get(x);
            for (String rightItem : rightItems) {
                String[] rightItemString = rightItem.split(" ");

                if (rightItemString.length == 1) {
                    first.addAll(FIRSTx(rightItemString[0]));
                } else {
                    for (int i = 0; i < rightItemString.length; i++) {
                        String rightItemSub = rightItemString[i];
                        if (endChars.contains(rightItemSub)) {
                            first.add(rightItemSub);
                            break;
                        } else {
                            HashSet<String> rightItemFirst = FIRSTx(rightItemSub);
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
        return first;
    }

    private static void get_first() {
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
            first.put(nonEndChar, FIRSTx(nonEndChar));
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
        initIterms();
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
