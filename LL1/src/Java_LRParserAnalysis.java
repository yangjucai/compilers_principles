import java.util.*;

//enum Status {
//    NOSEARCH, SEARCHING, SEARCHED
//}
//class Pair
//{
//    // Return a map entry (key-value pair) from the specified values
//    public static <T, U> Map.Entry<T, U> of(T first, U second) {
//        return new AbstractMap.SimpleEntry<>(first, second);
//    }
//}

public class Java_LRParserAnalysis
{
    private static ArrayList<Map.Entry<String,String>> productions;
    private static HashMap<String, HashSet<String>> first;
    private static HashSet<String> endChars;
    private static HashSet<String> nonEndChars;
    private static String start;

    private static ArrayList<Map.Entry<String,Integer>> prog = new ArrayList<>();
    private static HashMap<Map.Entry<Integer,String>,Map.Entry<String,Integer>> actionTable = new HashMap<>();
    private static HashMap<Map.Entry<Integer,String>,Integer> gotoTable = new HashMap<>();
    private static ArrayList<SetOfItems> collection = new ArrayList<>();
    private static int statusCnt = 0;
    static class Item{
        //item [left -> beforeDot · nonTerminal afterNonTerminal, lookAhead]
        private String left;
        private String beforeDot;
        private String afterDot;
        private String lookAhead;

        @Override
        public boolean equals(Object obj) {
            if(this == obj)
                return true;
            if(obj instanceof Item){
                Item tmp = (Item) obj;
                return this.left.equals(tmp.left) && this.beforeDot.equals(tmp.beforeDot) && this.afterDot.equals(tmp.afterDot) && this.lookAhead.equals(tmp.lookAhead);
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
                //contains each other -> equals
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
                            // traverse FIRST(afterNonTerminal lookAhead) terminal
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

    @SuppressWarnings( " unchecked " )
    private static void initIterms(){
        SetOfItems initStatus = new SetOfItems();
        initStatus.addItem(new Item("program'","","program","$"));
//        initStatus.addItem(new Item("S'","","S","$"));
        initStatus = CLOSURE(initStatus);
        initStatus.setStatusNum(statusCnt++);

        collection.add(initStatus);
        int lastItemNum = collection.size()-1;
        while(lastItemNum != collection.size()){
            lastItemNum = collection.size();
            ArrayList<SetOfItems> tmpC = new ArrayList<>();
            collection.forEach(items->{
                tmpC.add(items);
            });
            for(SetOfItems I:tmpC){
                //traverse every Char
                for(String X:endChars){
                    if(X.equals("E"))
                        continue;
                    SetOfItems NextI = GOTO(I,X);
                    if(collection.contains(NextI)){
                        int nextStatus = 0;
                        for(SetOfItems item: collection){
                            if(item.equals(NextI)){
                                nextStatus = item.statusNum;
                                break;
                            }
                        }
                        collection.get(I.statusNum).setGOTO(X,nextStatus);
                    }
                    else if(NextI.items.size() != 0){
                        NextI.setStatusNum(statusCnt++);
                        collection.get(I.statusNum).setGOTO(X,statusCnt-1);
                        collection.add(NextI);
                    }
                }
                for(String X:nonEndChars){
                    SetOfItems NextI = GOTO(I,X);
                    if(collection.contains(NextI)){
                        int nextStatus = 0;
                        for(SetOfItems item: collection){
                            if(item.equals(NextI)){
                                nextStatus = item.statusNum;
                                break;
                            }
                        }
                        collection.get(I.statusNum).setGOTO(X,nextStatus);
                    }
                    else if(NextI.items.size() != 0){
                        NextI.setStatusNum(statusCnt++);
                        collection.get(I.statusNum).setGOTO(X,statusCnt-1);
                        collection.add(NextI);
                    }
                }
            }
        }
//        for(SetOfItems closure: collection){
//            System.out.print(closure.statusNum+" ");
//
//            closure.GOTO.forEach((key,value)->{
//                System.out.print(key+"->"+value+" ");
//            });
//            System.out.print(" ");
//            System.out.print(closure.items.size()+" ");
//            for(Item item:closure.items){
//                System.out.print("["+item.left+" -> "+item.beforeDot+"."+item.afterDot+", "+item.lookAhead+"]; ");
//            }
//            System.out.println();
//        }
    }

    private static void init_data() {

        //init input
        read_prog();
        prog.add(Pair.of("$",0));

        //init production
        getProduction();
//        productions = new ArrayList<>();
//        productions.add(Pair.of("S'","S"));
//        productions.add(Pair.of("S","C C"));
//        productions.add(Pair.of("C","c C"));
//        productions.add(Pair.of("C","d"));

        //init start :program
        getStart();
//        start = "S";
        //init terminal
        getTernimal();
//        endChars = new HashSet<>();
//        endChars.add("c");
//        endChars.add("d");
//        endChars.add("E");

        //init nonterminal
        getNonTernimal();
//        nonEndChars = new HashSet<>();
//        nonEndChars.add("S");
//        nonEndChars.add("C");

        //init first
        first = new HashMap<>();
        getFirst();

        //init items
        initIterms();

        //get table
        getTable();

    }

    private static void getStart(){
        start = "program";
    }

    private static void getNonTernimal(){
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
    }
    private static void getTernimal(){
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
    }
    private static void getProduction(){
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

        productions.forEach(production->{
            System.out.println(production.getKey()+" -> "+production.getValue());
        });
    }

    private static void getTable(){
        for(SetOfItems items: collection){
            //get actionTable
            for(Item item:items.items){
                //deal with left -> E.
                boolean leftEqualsE = item.afterDot.equals("E");
                if(leftEqualsE)
                    item.afterDot = "";


                if(item.afterDot.equals("")){
                    // accept
                    if(item.beforeDot.equals(start)){
                        actionTable.put(Pair.of(items.statusNum, item.lookAhead),Pair.of("acc",0));
                    }
                    // reduction
                    else{
                        int productionNum = -1;
                        for(int i=0;i<productions.size();i++){
                            if(item.beforeDot.equals("") && item.afterDot.equals(""))
                                item.beforeDot = "E";
                            if(productions.get(i).getKey().equals(item.left) && productions.get(i).getValue().equals(item.beforeDot)){
                                productionNum = i;
                                break;
                            }
                        }
                        actionTable.put(Pair.of(items.statusNum, item.lookAhead),Pair.of("r",productionNum));
                    }
                }
                //shitf
                else{
                    String[] afterDotSubs = item.afterDot.trim().split(" ");
                    if(endChars.contains(afterDotSubs[0]) && items.GOTO.get(afterDotSubs[0]) != null){
                        int nextStatus = items.GOTO.get(afterDotSubs[0]);
                        actionTable.put(Pair.of(items.statusNum, afterDotSubs[0]),Pair.of("s",nextStatus));
                    }
                }

            }
            //get gotoTable
            items.GOTO.forEach((nonTerminal, nextStatus)->{
                if(nonEndChars.contains(nonTerminal))
                    gotoTable.put(Pair.of(items.statusNum, nonTerminal),nextStatus);
            });

        }


        //print
//        System.out.println("action table");
//        actionTable.forEach((point,action)->{
//            System.out.println("("+point.getKey()+","+point.getValue()+")->"+action.getKey()+action.getValue());
//        });
//        System.out.println("gotoTable");
//        gotoTable.forEach((point,gotoAction)->{
//            System.out.println("("+point.getKey()+","+point.getValue()+")->"+gotoAction);
//        });
    }

    private static HashSet<String> firstx(String x) {
        HashSet<String> first = new HashSet<>();

        //x is terminal，include E in this problem
        if (endChars.contains(x)) {
            first.add(x);
            return first;
        } else {
            //FIRST of right items
            for (Map.Entry<String,String> production:productions) {
                if(production.getKey().equals(x)){
                    String rightItem = production.getValue();
                    String[] rightItemString = rightItem.split(" ");
                    if (rightItemString.length == 1) {
                        first.addAll(firstx(rightItemString[0]));
                    } else {
                        for (int i = 0; i < rightItemString.length; i++) {
                            if(rightItemString[0].equals(x))
                                continue;
                            String rightItemSub = rightItemString[i];
                            if (endChars.contains(rightItemSub)) {
                                first.add(rightItemSub);
                                break;
                            } else {
                                HashSet<String> rightItemFirst = firstx(rightItemSub);
                                //contains null
                                if (rightItemFirst.contains("E")) {
                                    //rightItem is the last Char, add epsilon to FIRST
                                    if (i == rightItemString.length - 1) {
                                        first.addAll(rightItemFirst);
                                    } else {
                                        rightItemFirst.remove("E");
                                        first.addAll(rightItemFirst);
                                    }
                                }
                                //not contains null
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
        //terminal is itself
        for (String endChar : endChars) {
            HashSet<String> tmp = new HashSet<>();
            tmp.add(endChar);
            first.put(endChar, tmp);
        }
        //add "$"
        HashSet<String> dollar = new HashSet<>();
        dollar.add("$");
        first.put("$",dollar);

        //traverse nonterminal
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
            //Y1 contains null
            if (firstOfChar.contains("E")) {
                res.addAll(firstOfChar);
                res.remove("E");
            }
            //Y1 not contains null
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
        Deque<Map.Entry<String,String>> usedProduction = new ArrayDeque<>();
        Deque<SetOfItems> stack = new ArrayDeque<>();
        stack.push(collection.get(0));
        while(true){
            SetOfItems peek = stack.peek();
            String actionKey = actionTable.get(Pair.of(peek.statusNum,prog.get(0).getKey())) == null?null:actionTable.get(Pair.of(peek.statusNum,prog.get(0).getKey())).getKey();
            int actionValue = actionTable.get(Pair.of(peek.statusNum,prog.get(0).getKey())) == null?-1:actionTable.get(Pair.of(peek.statusNum,prog.get(0).getKey())).getValue();
            //error
            if(actionKey == null){
                prog.add(0,Pair.of(";",prog.get(0).getValue()));
                System.out.println("语法错误，第"+Integer.toString(prog.get(0).getValue()-1)+"行，缺少"+"\""+";"+"\"");
                continue;
            }
            //s shift
            else if(actionKey.equals("s")){
                stack.push(collection.get(actionValue));
                if(prog.size()>1)
                   prog.remove(0);
            }
            //r reduction
            else if(actionKey.equals("r")){
                Map.Entry<String,String> production = productions.get(actionValue);
                String[] rightItems = production.getValue().trim().split(" ");
                //when right is null
                boolean rightNotEqualsE = true;
                if(rightItems.length==1 && rightItems[0].equals("E"))
                    rightNotEqualsE = false;
                for(int i=0;i<rightItems.length && rightNotEqualsE;i++){
                    stack.pop();
                }
                stack.push(collection.get(gotoTable.get(Pair.of(stack.peek().statusNum,production.getKey()))));
                usedProduction.push(production);
//                System.out.println(production.getKey()+"->"+production.getValue());
            }
            //acc
            else{
                break;
            }

            //debug
//            System.out.println("action:"+actionKey+actionValue);
//            System.out.print("栈：");
//            stack.forEach(items ->{
//                System.out.print(items.statusNum + " ");
//            });
//            System.out.println();
//            System.out.print("输入：");
//            prog.forEach(input->{
//                System.out.print(input.getKey());
//            });
//            System.out.println();
        }
        //print
        Deque<String> output = new ArrayDeque<>();
        output.addLast(start);
        System.out.println(getOutput(output)+" => ");
        int cnt = 0;
        for (Map.Entry<String, String> production : usedProduction) {
            Deque<String> tmp = new ArrayDeque<>();
            while(!output.isEmpty()){
                String peek = output.removeLast();
                if(peek.equals(production.getKey())){
                    String[] rightItems = production.getValue().trim().split(" ");
                    //push in reverse sequence
                    for(int i=0; i< rightItems.length;i++) {
                        if(rightItems[i].equals("E"))
                            continue;
                        output.addLast(rightItems[i]);
                    }
                    break;
                }
                else{
                    tmp.addFirst(peek);
                }
            }
            //tmp put back to output
            while(!tmp.isEmpty()){
                output.addLast(tmp.removeFirst());
            }
            System.out.print(getOutput(output));
            if(++cnt != usedProduction.size())
                System.out.print(" =>");
            System.out.println(" ");
        }

    }

    private static String getOutput(Deque<String> output){
        String res = "";
        for (String s : output) {
            res += s + " ";

        }
        return res.trim();
    }

    /**
     * this is the main method
     * @param args
     */
    public static void main(String[] args) {
        init_data();
        analysis();
    }
}
