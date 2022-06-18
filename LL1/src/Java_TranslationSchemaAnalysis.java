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

public class Java_TranslationSchemaAnalysis {
    private static ArrayList<Map.Entry<String, String>> productions;
    private static HashMap<String, HashSet<String>> first;
    private static HashSet<String> endChars;
    private static HashSet<String> nonEndChars;
    private static String start;

    private static ArrayList<Integer> prog = new ArrayList<>();
    private static ArrayList<Lexical> symbolProduced = new ArrayList<>();
    private static HashMap<Map.Entry<Integer, String>, Map.Entry<String, Integer>> actionTable = new HashMap<>();
    private static HashMap<Map.Entry<Integer, String>, Integer> gotoTable = new HashMap<>();
    private static ArrayList<SetOfItems> collection = new ArrayList<>();
    private static ArrayList<Lexical> lexicals = new ArrayList<>();
    private static int lexicalCnt = 0;
    private static int statusCnt = 0;
    private static boolean noCompilerError = true;
    private static String errorLog = "";

    static class Lexical {
        private String name;
        private String identifier;
        private int lineNum;
        private String type;
        private Float value;

        public Lexical(String name, String identifier, int lineNum, String type, Float value) {
            this.name = name;
            this.identifier = identifier;
            this.lineNum = lineNum;
            this.type = type;
            this.value = value;
        }

        public Lexical clone() {
            return new Lexical(this.name, this.identifier, this.lineNum, this.type, this.value);
        }
    }

    static class Item {
        //item [left -> beforeDot · nonTerminal afterNonTerminal, lookAhead]
        private String left;
        private String beforeDot;
        private String afterDot;
        private String lookAhead;

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj instanceof Item) {
                Item tmp = (Item) obj;
                return this.left.equals(tmp.left) && this.beforeDot.equals(tmp.beforeDot) && this.afterDot.equals(tmp.afterDot) && this.lookAhead.equals(tmp.lookAhead);
            } else
                return false;
        }

        public Item(String left, String beforeDot, String afterDot, String lookAhead) {
            this.left = left;
            this.beforeDot = beforeDot;
            this.afterDot = afterDot;
            this.lookAhead = lookAhead;

        }
    }

    static class SetOfItems {
        public Deque<Item> items;
        public HashMap<String, Integer> GOTO;
        public int statusNum;

        public SetOfItems() {
            this.items = new ArrayDeque<>();
            this.statusNum = 0;
            GOTO = new HashMap<>();
        }

        public void setGOTO(String X, int nextStatus) {
            this.GOTO.put(X, nextStatus);
        }

        public void setStatusNum(int statusNum) {
            this.statusNum = statusNum;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj instanceof SetOfItems) {
                //contains each other -> equals
                for (Item item : this.items) {
                    if (!((SetOfItems) obj).items.contains(item))
                        return false;
                }
                for (Item item : ((SetOfItems) obj).items) {
                    if (!this.items.contains(item))
                        return false;
                }
                return true;
            } else
                return false;
        }

        private void addItem(Item item) {
            if (!this.items.contains(item))
                this.items.add(item);
        }
    }

    static SetOfItems CLOSURE(SetOfItems I) {
        int lastItemNum = I.items.size() - 1;
        while (lastItemNum != I.items.size()) {
            lastItemNum = I.items.size();
            Deque<Item> tmpItems = ((ArrayDeque<Item>) I.items).clone();
            for (Item item : tmpItems) {
                String[] afterDotSubs = item.afterDot.trim().split(" ");
                String nonTerminal = nonEndChars.contains(afterDotSubs[0]) ? afterDotSubs[0] : "";
                if (nonTerminal != "") {
                    //遍历G'中item.nonTerminal -> rights
                    for (Map.Entry<String, String> production : productions) {
                        if (production.getKey().equals(nonTerminal)) {
                            String right = production.getValue();
                            // traverse FIRST(afterNonTerminal lookAhead) terminal
                            String afterNonTerminal = "";
                            for (int i = 1; i < afterDotSubs.length; i++) {
                                afterNonTerminal = afterNonTerminal + " " + afterDotSubs[i];
                            }
                            HashSet<String> first = get_rightItems_first(afterNonTerminal + " " + item.lookAhead);
                            String left = nonTerminal;
                            String beforeDot = "";
                            String afterDot = right;
                            for (String terminal : first) {
                                I.addItem(new Item(left, beforeDot, afterDot, terminal));
                            }
                        }

                    }
                }
            }
        }

        return I;
    }

    static SetOfItems GOTO(SetOfItems I, String nonTerminal) {
        SetOfItems J = new SetOfItems();
        for (Item item : I.items) {
            String[] afterDotSubs = item.afterDot.trim().split(" ");
            if (afterDotSubs[0].equals(nonTerminal)) {
                String left0 = item.left;
                String beforeDot0 = "";
                String afterDot0 = "";
                String lookAhead0 = item.lookAhead;
                if (afterDotSubs.length > 0) {
                    String nextChar = afterDotSubs[0];
                    beforeDot0 = (item.beforeDot + " " + nextChar).trim();
                    for (int i = 1; i < afterDotSubs.length; i++) {
                        afterDot0 = afterDot0 + " " + afterDotSubs[i];
                    }
                    afterDot0 = afterDot0.trim();
                }
                Item newItem = new Item(left0, beforeDot0, afterDot0, lookAhead0);
                J.addItem(newItem);

            }

        }
        return CLOSURE(J);
    }

    private static void initIterms() {
        SetOfItems initStatus = new SetOfItems();
        initStatus.addItem(new Item("program'", "", "program", "$"));
//        initStatus.addItem(new Item("S'","","S","$"));
        initStatus = CLOSURE(initStatus);
        initStatus.setStatusNum(statusCnt++);

        collection.add(initStatus);
        int lastItemNum = collection.size() - 1;
        while (lastItemNum != collection.size()) {
            lastItemNum = collection.size();
            ArrayList<SetOfItems> tmpC = new ArrayList<>();
            collection.forEach(items -> {
                tmpC.add(items);
            });
            for (SetOfItems I : tmpC) {
                //traverse every Char
                for (String X : endChars) {
                    if (X.equals("E"))
                        continue;
                    SetOfItems NextI = GOTO(I, X);
                    if (collection.contains(NextI)) {
                        int nextStatus = 0;
                        for (SetOfItems item : collection) {
                            if (item.equals(NextI)) {
                                nextStatus = item.statusNum;
                                break;
                            }
                        }
                        collection.get(I.statusNum).setGOTO(X, nextStatus);
                    } else if (NextI.items.size() != 0) {
                        NextI.setStatusNum(statusCnt++);
                        collection.get(I.statusNum).setGOTO(X, statusCnt - 1);
                        collection.add(NextI);
                    }
                }
                for (String X : nonEndChars) {
                    SetOfItems NextI = GOTO(I, X);
                    if (collection.contains(NextI)) {
                        int nextStatus = 0;
                        for (SetOfItems item : collection) {
                            if (item.equals(NextI)) {
                                nextStatus = item.statusNum;
                                break;
                            }
                        }
                        collection.get(I.statusNum).setGOTO(X, nextStatus);
                    } else if (NextI.items.size() != 0) {
                        NextI.setStatusNum(statusCnt++);
                        collection.get(I.statusNum).setGOTO(X, statusCnt - 1);
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

        //init input
        read_prog();
        lexicals.add(new Lexical("$", "$", -1, "other", Float.MAX_VALUE));
        prog.add(lexicalCnt++);

        //init production
        getProduction();
//        productions = new ArrayList<>();
//        productions.add(Pair.of("S'","S"));
//        productions.add(Pair.of("S","C C"));
//        productions.add(Pair.of("C","c C"));
//        productions.add(Pair.of("C","d"));


        //init first
        first = new HashMap<>();
        getFirst();

        //init items
        initIterms();

        //get table
        getTable();

    }

    private static void getStart() {
        start = "program";
    }

    private static void getNonTernimal() {
        nonEndChars = new HashSet<>();
        nonEndChars.add("program");
        nonEndChars.add("decls");
        nonEndChars.add("decl");
        nonEndChars.add("stmt");
        nonEndChars.add("compoundstmt");
        nonEndChars.add("stmts");
        nonEndChars.add("ifstmt");
        nonEndChars.add("assgstmt");
        nonEndChars.add("boolexpr");
        nonEndChars.add("boolop");
        nonEndChars.add("arithexpr");
        nonEndChars.add("arithexprprime");
        nonEndChars.add("multexpr");
        nonEndChars.add("multexprprime");
        nonEndChars.add("simpleexpr");
    }

    private static void getTernimal() {
        endChars = new HashSet<>();
        endChars.add("{");
        endChars.add("}");
        endChars.add("if");
        endChars.add("(");
        endChars.add(")");
        endChars.add("then");
        endChars.add("else");
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
        endChars.add("INTNUM");
        endChars.add("REALNUM");
        endChars.add("int");
        endChars.add("real");
        endChars.add("E");
        endChars.add(";");
    }

    private static void getProduction() {
        productions = new ArrayList<>();
        productions.add(Pair.of("program'", "program"));
        productions.add(Pair.of("program", "decls compoundstmt"));
        productions.add(Pair.of("decls", "decl ; decls"));
        productions.add(Pair.of("decls", "E"));
        productions.add(Pair.of("decl", "int ID = INTNUM"));
        productions.add(Pair.of("decl", "real ID = REALNUM"));
        productions.add(Pair.of("stmt", "ifstmt"));
        productions.add(Pair.of("stmt", "assgstmt"));
        productions.add(Pair.of("stmt", "compoundstmt"));
        productions.add(Pair.of("compoundstmt", "{ stmts }"));
        productions.add(Pair.of("stmts", "stmt stmts"));
        productions.add(Pair.of("stmts", "E"));
        productions.add(Pair.of("ifstmt", "if ( boolexpr ) then stmt else stmt"));
        productions.add(Pair.of("assgstmt", "ID = arithexpr ;"));
        productions.add(Pair.of("boolexpr", "arithexpr boolop arithexpr"));
        productions.add(Pair.of("boolop", "<"));
        productions.add(Pair.of("boolop", ">"));
        productions.add(Pair.of("boolop", "<="));
        productions.add(Pair.of("boolop", ">="));
        productions.add(Pair.of("boolop", "=="));
        productions.add(Pair.of("arithexpr", "multexpr arithexprprime"));
        productions.add(Pair.of("arithexprprime", "+ multexpr arithexprprime"));
        productions.add(Pair.of("arithexprprime", "- multexpr arithexprprime"));
        productions.add(Pair.of("arithexprprime", "E"));
        productions.add(Pair.of("multexpr", "simpleexpr multexprprime"));
        productions.add(Pair.of("multexprprime", "* simpleexpr multexprprime"));
        productions.add(Pair.of("multexprprime", "/ simpleexpr multexprprime"));
        productions.add(Pair.of("multexprprime", "E"));
        productions.add(Pair.of("simpleexpr", "ID"));
        productions.add(Pair.of("simpleexpr", "INTNUM"));
        productions.add(Pair.of("simpleexpr", "REALNUM"));
        productions.add(Pair.of("simpleexpr", "( arithexpr )"));

//        for (int i = 0; i < productions.size(); i++) {
//            System.out.println(i+" "+productions.get(i).getKey()+" -> "+productions.get(i).getValue());
//        }
    }

    private static void getTable() {
        for (SetOfItems items : collection) {
            //get actionTable
            for (Item item : items.items) {
                //deal with left -> E.
                boolean leftEqualsE = item.afterDot.equals("E");
                if (leftEqualsE)
                    item.afterDot = "";


                if (item.afterDot.equals("")) {
                    // accept
                    if (item.beforeDot.equals(start)) {
                        actionTable.put(Pair.of(items.statusNum, item.lookAhead), Pair.of("acc", 0));
                    }
                    // reduction
                    else {
                        int productionNum = -1;
                        for (int i = 0; i < productions.size(); i++) {
                            if (item.beforeDot.equals("") && item.afterDot.equals(""))
                                item.beforeDot = "E";
                            if (productions.get(i).getKey().equals(item.left) && productions.get(i).getValue().equals(item.beforeDot)) {
                                productionNum = i;
                                break;
                            }
                        }
                        actionTable.put(Pair.of(items.statusNum, item.lookAhead), Pair.of("r", productionNum));
                    }
                }
                //shitf
                else {
                    String[] afterDotSubs = item.afterDot.trim().split(" ");
                    if (endChars.contains(afterDotSubs[0]) && items.GOTO.get(afterDotSubs[0]) != null) {
                        int nextStatus = items.GOTO.get(afterDotSubs[0]);
                        actionTable.put(Pair.of(items.statusNum, afterDotSubs[0]), Pair.of("s", nextStatus));
                    }
                }

            }
            //get gotoTable
            items.GOTO.forEach((nonTerminal, nextStatus) -> {
                if (nonEndChars.contains(nonTerminal))
                    gotoTable.put(Pair.of(items.statusNum, nonTerminal), nextStatus);
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
            for (Map.Entry<String, String> production : productions) {
                if (production.getKey().equals(x)) {
                    String rightItem = production.getValue();
                    String[] rightItemString = rightItem.split(" ");
                    if (rightItemString.length == 1) {
                        first.addAll(firstx(rightItemString[0]));
                    } else {
                        for (int i = 0; i < rightItemString.length; i++) {
                            if (rightItemString[0].equals(x))
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
        first.put("$", dollar);

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
     * this method is to read the standard input
     */
    private static void read_prog() {
        Scanner sc = new Scanner(System.in);
        Integer lineNum = 1;

        while (sc.hasNextLine()) {
            String line = sc.nextLine();
            String[] tmp = line.split(" ");
            for (String Char : tmp) {
                if (Char.equals(""))
                    continue;
                boolean notExist = true;
                for (int i = 0; i < lexicals.size(); i++) {
                    if (lexicals.get(i).identifier.equals(Char)) {
                        notExist = false;
                        prog.add(i);
                        break;
                    }
                }
                if (notExist) {
                    if (Char.matches("^[a-z]$")) {
                        lexicals.add(new Lexical("ID", Char, lineNum, "INTNUMorREALNUM", Float.MAX_VALUE));
                    } else if (Char.matches("^[0-9]+.[0-9]+$")) {
                        lexicals.add(new Lexical("REALNUM", Char, lineNum, "REALNUM", Float.parseFloat(Char)));
                    } else if (Char.matches("^[0-9]+$")) {
                        lexicals.add(new Lexical("INTNUM", Char, lineNum, "INTNUM", Float.parseFloat(Char)));
                    } else {
                        lexicals.add(new Lexical(Char, Char, lineNum, "other", Float.MAX_VALUE));
                    }
                    prog.add(lexicalCnt++);
                }
            }
            lineNum++;
        }

        //add lexicals
        for (String nonEndChar : nonEndChars) {
            boolean notExist = true;
            for (int i = 0; i < lexicals.size(); i++) {
                if (lexicals.get(i).name.equals(nonEndChar)) {
                    notExist = false;
                    break;
                }
            }
            if (notExist)
                lexicals.add(lexicalCnt++, new Lexical(nonEndChar, nonEndChar, lineNum, "other", Float.MAX_VALUE));
        }
    }


    // add your method here!!


    /**
     * you should add some code in this method to achieve this lab
     */

    private static void analysis() {
        Deque<Map.Entry<String, String>> usedProduction = new ArrayDeque<>();
        Deque<SetOfItems> stack = new ArrayDeque<>();
        stack.push(collection.get(0));
        while (true) {
            SetOfItems peek = stack.peek();
            String actionKey = actionTable.get(Pair.of(peek.statusNum, lexicals.get(prog.get(0)).name)) == null ? null : actionTable.get(Pair.of(peek.statusNum, lexicals.get(prog.get(0)).name)).getKey();
            int actionValue = actionTable.get(Pair.of(peek.statusNum, lexicals.get(prog.get(0)).name)) == null ? -1 : actionTable.get(Pair.of(peek.statusNum, lexicals.get(prog.get(0)).name)).getValue();

//            for (int i = symbolProduced.size()-1; i >= 0; i--) {
//                System.out.print(symbolProduced.get(i).identifier+" ");
//            }
//            System.out.println();

            //error
            if (actionKey == null) {
                if (lexicals.get(prog.get(0)).type.equals("INTNUM")) {
                    if (symbolProduced.get(2).name.equals("real")) {
                        errorLog += "error message:line " + lexicals.get(prog.get(0)).lineNum + ",intnum can not be translated into real type\n";
                        noCompilerError = false;
                        lexicals.get(prog.get(0)).type = "REALNUM";
                        lexicals.get(prog.get(0)).name = "REALNUM";
                        continue;
                    }
                } else if (lexicals.get(prog.get(0)).type.equals("REALNUM")) {
                    if (symbolProduced.get(2).name.equals("int")) {
                        errorLog += "error message:line " + lexicals.get(prog.get(0)).lineNum + ",realnum can not be translated into int type\n";
                        noCompilerError = false;
                        lexicals.get(prog.get(0)).type = "INTNUM";
                        lexicals.get(prog.get(0)).name = "INTNUM";
                        continue;
                    }
                } else {
                    System.out.println("语法错误");
                    break;
                }
            }
            //s shift
            else if (actionKey.equals("s")) {
                stack.push(collection.get(actionValue));
                //移入prog首符号到处理过的符号表
                symbolProduced.add(0, lexicals.get(prog.get(0)).clone());
//                System.out.println("移入"+symbolProduced.get(0).identifier);
                if (prog.size() > 1)
                    prog.remove(0);


            }
            //r reduction
            else if (actionKey.equals("r")) {
                Map.Entry<String, String> production = productions.get(actionValue);
                String[] rightItems = production.getValue().trim().split(" ");
                //when right is null
                boolean rightNotEqualsE = true;
                if (rightItems.length == 1 && rightItems[0].equals("E")) {
                    rightNotEqualsE = false;

                    boolean notExist = true;
                    for (int i = 0; i < lexicals.size(); i++) {
                        if (lexicals.get(i).name.equals(production.getKey())) {
                            notExist = false;
                            symbolProduced.add(0, lexicals.get(i).clone());
//                            System.out.println("遇空移入"+symbolProduced.get(0).identifier);
                            break;
                        }
                    }
                    if (notExist) {
                        lexicals.add(new Lexical(production.getKey(), production.getKey(), -1, "other", Float.MAX_VALUE));
                        symbolProduced.add(0, lexicals.get(lexicals.size() - 1).clone());
//                        System.out.println("遇空移入"+symbolProduced.get(0).identifier);
                    }
                }
                for (int i = 0; i < rightItems.length && rightNotEqualsE; i++) {
                    stack.pop();
                }
                stack.push(collection.get(gotoTable.get(Pair.of(stack.peek().statusNum, production.getKey()))));
                usedProduction.push(production);

                //处理符号表 并 更改需要更改的属性值
                switch (actionValue) {
                    case 4:
                        //使用产生式4 decl -> int ID = INTNUM
                        //赋值语句类型不匹配
                        if (!symbolProduced.get(0).type.equals("INTNUM")) {
                            errorLog += "error message:line " + symbolProduced.get(0).lineNum + ", realnum can not be translated into int type\n";
                            break;
                        } else {
                            //设置ID的type
                            for (Lexical lexical : lexicals) {
                                if(lexical.identifier.equals(symbolProduced.get(2).identifier)){
                                    lexical.type = "INTNUM";
                                    break;
                                }
                            }

                            symbolProduced.get(2).value = symbolProduced.get(0).value;
                            for (Lexical lexical : lexicals) {
                                if (lexical.identifier.equals(symbolProduced.get(2).identifier)) {
                                    lexical.value = symbolProduced.get(2).value;
                                    break;
                                }
                            }
                        }
                        break;
                    case 5:
                        //使用产生式5 decl -> real ID = REALNUM
                        if (!symbolProduced.get(0).type.equals("REALNUM")) {
                            errorLog += "error message:line " + symbolProduced.get(0).lineNum + ",intnum can not be translated into real type\n";
                            break;
                        } else {
                            //设置ID的type
                            for (Lexical lexical : lexicals) {
                                if(lexical.identifier.equals(symbolProduced.get(2).identifier)){
                                    lexical.type = "REALNUM";
                                    break;
                                }
                            }

                            symbolProduced.get(2).value = symbolProduced.get(0).value;
                            for (Lexical lexical : lexicals) {
                                if (lexical.identifier.equals(symbolProduced.get(2).identifier))
                                    lexical.value = symbolProduced.get(2).value;
                            }
                        }
                        break;
                    case 13:
                        //使用产生式13 assgstmt -> ID = arithexpr ;
                        if (symbolProduced.get(1).type.equals(symbolProduced.get(3).type)) {
                            errorLog += "error message:line " + symbolProduced.get(0).lineNum + "," + symbolProduced.get(1).type.toLowerCase() + " can not be translated into " + symbolProduced.get(3).type.toLowerCase() + " type\n";
                            break;
                        }
                        //boolexpr: Float.MAX_VALUE表示true, Float.MIN_VALUE表示false
                        else if (symbolProduced.get(4).name.equals("then") || symbolProduced.get(4).name.equals("else")) {
                            if ((symbolProduced.get(4).name.equals("then") && symbolProduced.get(6).value == Float.MAX_VALUE) || (symbolProduced.get(4).name.equals("else") && symbolProduced.get(8).value == Float.MIN_VALUE)) {
                                symbolProduced.get(3).value = symbolProduced.get(1).value;
                                for (Lexical lexical : lexicals) {
                                    if (lexical.identifier.equals(symbolProduced.get(3).identifier))
                                        lexical.value = symbolProduced.get(3).value;
                                }
                            }
                        } else {
                            symbolProduced.get(3).value = symbolProduced.get(1).value;
                            for (Lexical lexical : lexicals) {
                                if (lexical.identifier.equals(symbolProduced.get(3).identifier))
                                    lexical.value = symbolProduced.get(3).value;
                            }
                        }
                        break;
                    case 14:
                        //使用产生式14 boolexpr -> arithexpr boolop arithexpr
                        Float left = symbolProduced.get(2).value, right = symbolProduced.get(0).value;
                        Float boolexpr;//存储比较结果，Float.MAX_VALUE表示true, Float.MIN_VALUE表示false
                        switch (symbolProduced.get(1).identifier) {
                            case "<":
                                if (left < right)
                                    boolexpr = Float.MAX_VALUE;
                                else boolexpr = Float.MIN_VALUE;
                                break;
                            case ">":
                                if (left > right)
                                    boolexpr = Float.MAX_VALUE;
                                else boolexpr = Float.MIN_VALUE;
                                break;
                            case "<=":
                                if (left <= right)
                                    boolexpr = Float.MAX_VALUE;
                                else boolexpr = Float.MIN_VALUE;
                                break;
                            case ">=":
                                if (left >= right)
                                    boolexpr = Float.MAX_VALUE;
                                else boolexpr = Float.MIN_VALUE;
                                break;
                            default:
                                if (left == right)
                                    boolexpr = Float.MAX_VALUE;
                                else boolexpr = Float.MIN_VALUE;
                        }
                        for (Lexical lexical : lexicals) {
                            if (lexical.name.equals("boolexpr")) {
                                lexical.value = boolexpr;
                                break;
                            }
                        }
                        break;
                    case 15:
                        for (Lexical lexical : lexicals) {
                            if (lexical.name.equals("boolop")) {
                                lexical.identifier = "<";
                            }
                        }
                        break;
                    case 16:
                        for (Lexical lexical : lexicals) {
                            if (lexical.name.equals("boolop")) {
                                lexical.identifier = ">";
                            }
                        }
                        break;
                    case 17:
                        for (Lexical lexical : lexicals) {
                            if (lexical.name.equals("boolop")) {
                                lexical.identifier = "<=";
                            }
                        }
                        break;
                    case 18:
                        for (Lexical lexical : lexicals) {
                            if (lexical.name.equals("boolop")) {
                                lexical.identifier = ">=";
                            }
                        }
                        break;
                    case 19:
                        for (Lexical lexical : lexicals) {
                            if (lexical.name.equals("boolop")) {
                                lexical.identifier = "==";
                            }
                        }
                        break;
                    case 28:
                        //使用产生式28 simpleexpr -> ID
                        for (Lexical lexical : lexicals) {
                            if (lexical.identifier.equals("simpleexpr")) {
                                lexical.value = symbolProduced.get(0).value;
                            }
                        }
                        break;
                    case 29:
                        //使用产生式29 simpleexpr -> INTNUM
                        for (Lexical lexical : lexicals) {
                            if (lexical.identifier.equals("simpleexpr")) {
                                lexical.value = symbolProduced.get(0).value;
                            }
                        }
                        break;
                    case 30:
                        //使用产生式30 simpleexpr -> REALNUM
                        for (Lexical lexical : lexicals) {
                            if (lexical.identifier.equals("simpleexpr")) {
                                lexical.value = symbolProduced.get(0).value;
                            }
                        }
                        break;
                    case 31:
                        //使用产生式31 simpleexpr -> ( arithexpr )
                        for (Lexical lexical : lexicals) {
                            if (lexical.identifier.equals("simpleexpr")) {
                                lexical.value = symbolProduced.get(1).value;
                            }
                        }
                        break;

                    case 21:
                        //现在处理过的符号为......multexpr + multexpr arithexprprime
                        symbolProduced.get(3).value += symbolProduced.get(1).value;
                        break;
                    case 22:
                        symbolProduced.get(3).value -= symbolProduced.get(1).value;
                        break;
                    case 20:
                        //使用产生式20 arithexpr -> multexpr arithexprprime
                        for (Lexical lexical : lexicals) {
                            if (lexical.identifier.equals("arithexpr")) {
                                lexical.value = symbolProduced.get(1).value;
                            }
                        }
                        break;
                    case 25:
                        symbolProduced.get(3).value *= symbolProduced.get(1).value;
                        break;
                    case 26:
                        if (symbolProduced.get(1).value == 0) {
                            errorLog += "error message:line 5,division by zero\n";
                        } else {
                            symbolProduced.get(3).value /= symbolProduced.get(1).value;
                        }
                        break;
                    case 24:
                        //24 multexpr -> simpleexpr multexprprime
                        for (Lexical lexical : lexicals) {
                            if (lexical.identifier.equals("multexpr")) {
                                lexical.value = symbolProduced.get(1).value;
                            }
                        }
                        break;
                    default:
                        break;
                }

                for (int i = 0; i < rightItems.length; i++) {
//                    System.out.println("移出"+symbolProduced.get(0).identifier);
                    symbolProduced.remove(0);
                }
                boolean notExist = true;
                for (int i = 0; i < lexicals.size(); i++) {
                    if (lexicals.get(i).name.equals(production.getKey())) {
                        notExist = false;
                        symbolProduced.add(0, lexicals.get(i).clone());
//                        System.out.println("移出后移入"+symbolProduced.get(0).identifier);
                        break;
                    }
                }
                if (notExist) {
                    lexicals.add(new Lexical(production.getKey(), production.getKey(), -1, "other", Float.MAX_VALUE));
                    symbolProduced.add(0, lexicals.get(lexicals.size() - 1).clone());
//                    System.out.println("移出后移入"+symbolProduced.get(0).identifier);
                }

//                for (Lexical lexical : lexicals) {
//                    System.out.print(lexical.identifier+":"+lexical.value+" ");
//                }
//                System.out.println("---------------------------");

            }
            //acc
            else {
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
//        Deque<String> output = new ArrayDeque<>();
//        output.addLast(start);
//        System.out.println(getOutput(output)+" => ");
//        int cnt = 0;
//        for (Map.Entry<String, String> production : usedProduction) {
//            Deque<String> tmp = new ArrayDeque<>();
//            while(!output.isEmpty()){
//                String peek = output.removeLast();
//                if(peek.equals(production.getKey())){
//                    String[] rightItems = production.getValue().trim().split(" ");
//                    //push in reverse sequence
//                    for(int i=0; i< rightItems.length;i++) {
//                        if(rightItems[i].equals("E"))
//                            continue;
//                        output.addLast(rightItems[i]);
//                    }
//                    break;
//                }
//                else{
//                    tmp.addFirst(peek);
//                }
//            }
//            //tmp put back to output
//            while(!tmp.isEmpty()){
//                output.addLast(tmp.removeFirst());
//            }
//            System.out.print(getOutput(output));
//            if(++cnt != usedProduction.size())
//                System.out.print(" =>");
//            System.out.println(" ");
//        }

        //print answer
        if(noCompilerError){
            for (Lexical lexical : lexicals) {
                if(lexical.name.equals("ID")){
                    String value;
                    if(lexical.type.equals("INTNUM")) {
                        value = Integer.toString(lexical.value.intValue());
                    }
                    else {
                        float f = (float) Math.round(lexical.value*100)/100;
                        value=Float.toString(f);
                    }
                    System.out.println(lexical.identifier+": "+value);
                }
            }
        }
        else{
            System.out.println(errorLog);
        }

    }

    private static String getOutput(Deque<String> output) {
        String res = "";
        for (String s : output) {
            res += s + " ";

        }
        return res.trim();
    }

    /**
     * this is the main method
     *
     * @param args
     */
    public static void main(String[] args) {
        init_data();
        analysis();
    }
}
