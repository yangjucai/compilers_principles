import java.util.*;
import java.util.AbstractMap;
import java.util.Map;

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

public class Java_LLParserAnalysis {
    private static HashMap<String, String[]> rule;
    private static HashMap<String, HashSet<String>> first;
    private static HashMap<String, HashSet<String>> follow;
    private static HashSet<String> endChars;
    private static HashSet<String> nonEndChars;
    private static String start;
    //table: (非终结符，终结符)，（产生式左部，产生式右部）
    private static HashMap<Map.Entry<String, String>, Map.Entry<String, String>> table;

    /**
     * status存储查找FOLLOW集合时非终结符的状态
     * 状态NOSEARCH表示还没找过
     * 状态SEARCHING表示正在查找
     * 状态SEARCHED表示已经结束查找
     **/
    private static HashMap<String, Status> status;

    private static ArrayList<Map.Entry<String,Integer>> prog = new ArrayList<>();
    /**
     * status存储查找FOLLOW集合时非终结符的状态
     * 状态NOSEARCH表示还没找过
     * 状态SEARCHING表示正在查找
     * 状态SEARCHED表示已经结束查找
     **/

    private static void init_data() {

        //init rule
        rule = new HashMap<>();
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

        //init vt
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


        //init vn
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

        //init follow
        follow = new HashMap<>();
        get_follow();

        //init table
        table = new HashMap<>();
        get_table();

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

        //遍历非终结符
        for (String nonEndChar : nonEndChars) {
            first.put(nonEndChar, FIRSTx(nonEndChar));
        }
    }

    private static HashSet<String> FOLLOWx(String x) {
        //设置正在查找的非终结符状态为2
        status.put(x, Status.SEARCHING);

        //产生式中搜索所有非终结符出现的位置
        //遍历rule
        for (String nonEndChar : nonEndChars) {
            String[] rightItems = rule.get(nonEndChar);
            //遍历右部
            RightItemLoop:
            for (String rightItem : rightItems) {
                String[] rightItemString = rightItem.split(" ");
                //遍历右部中的每个字符串
                for (int i = 0; i < rightItemString.length; i++) {
                    String rightItemSub = rightItemString[i];
                    if (rightItemSub.equals(x)) {
                        //如果没在最右边
                        if (i < rightItemString.length - 1) {
                            //判断后一个字符是否为非终结符
                            for (int j = i + 1; j < rightItemString.length; j++) {
                                String nextItem = rightItemString[j];
                                //如果下一个字符是非终极符，查看FIRST集是否包含空串
                                if (nonEndChars.contains(nextItem)) {
                                    HashSet<String> nextFirst = first.get(nextItem);
                                    //如果包含空串
                                    if (nextFirst.contains("E")) {
                                        //如果是最后一个字符
                                        if (j == rightItemString.length - 1) {
                                            /**
                                             * 首先判断非终结符状态
                                             * 如果为正在查找，会陷入死循环
                                             * 所以要略过这一条产生式
                                             * 略过之前加上之前正在查找的非终结符的FOLLOW集合的元素。
                                             */
                                            if (status.get(nonEndChar) == Status.SEARCHING) {
                                                HashSet<String> follow_tmp = follow.get(nonEndChar);
                                                if (!follow_tmp.isEmpty()) {
                                                    follow.get(x).addAll(follow_tmp);
                                                }
                                                continue RightItemLoop;
                                            }
                                            HashSet<String> leftFOLLOW = FOLLOWx(nonEndChar);
                                            HashSet<String> nextFirstExceptNull = new HashSet<>(nextFirst);
                                            nextFirstExceptNull.remove("E");
                                            follow.get(x).addAll(leftFOLLOW);
                                            follow.get(x).addAll(nextFirstExceptNull);
                                        }
                                        //如果不是最后一个字符
                                        else {
                                            HashSet<String> nextFirstExceptNULL = new HashSet<>(nextFirst);
                                            nextFirstExceptNULL.remove("E");
                                            follow.get(x).addAll(nextFirstExceptNULL);
                                        }
                                    }
                                    //如果不包含空串
                                    else {
                                        follow.get(x).addAll(nextFirst);
                                        break;
                                    }
                                }
                                //如果下一个字符是终结符
                                else {
                                    follow.get(rightItemSub).add(nextItem);
                                    break;
                                }
                            }
                        } else {
                            /**
                             * 首先判断非终结符状态
                             * 如果为正在查找，会陷入死循环
                             * 所以要略过这一条产生式
                             * 略过之前加上之前正在查找的非终结符的FOLLOW集合的元素。
                             */
                            if (status.get(nonEndChar) == Status.SEARCHING) {
                                HashSet<String> follow_tmp = follow.get(nonEndChar);
                                if (!follow_tmp.isEmpty()) {
                                    follow.get(x).addAll(follow_tmp);
                                }
                                continue RightItemLoop;
                            }
                            //如果在最右边
                            HashSet<String> leftFOLLOW = FOLLOWx(nonEndChar);
                            follow.get(x).addAll(leftFOLLOW);
                        }
                    }
                }
            }
        }
        status.put(x, Status.SEARCHED);
        return follow.get(x);
    }

    private static void get_follow() {
        //init status
        status = new HashMap<>();
        //init follow
        for (String nonEndChar : nonEndChars) {
            status.put(nonEndChar, Status.NOSEARCH);
            HashSet<String> tmp = new HashSet<>();
            follow.put(nonEndChar, tmp);
        }

        HashSet<String> startFollow = new HashSet<>();
        startFollow.add("$");
        follow.put(start, startFollow);

        //遍历非终结符
        for (String nonEndChar : nonEndChars) {
            if (status.get(nonEndChar) == Status.SEARCHED) {
                continue;
            }
            FOLLOWx(nonEndChar);
        }
    }

    private static void get_table() {
        for (String nonEndChar : nonEndChars) {
            String[] rightItems = rule.get(nonEndChar);
            for (String rightItem : rightItems) {
                //产生式：nonEndChar -> rightItem

                HashSet<String> rightFirst = get_right_first(rightItem);
                //nonEndChar -> rightItem

                //FIRST(rightItemSub)有空，对FOLLOW(nonEndChar)中的每个符号b,
                // nonEndChar -> rightItem加入M[nonEndChar,b]中
                if (rightFirst.contains("E")) {
                    HashSet<String> leftFollow = follow.get(nonEndChar);
                    for (String b : leftFollow) {
                        table.put(Pair.of(nonEndChar, b), Pair.of(nonEndChar, rightItem));
                    }

                    rightFirst.remove("E");
                }
                //FIRST(rightItemSub)中的每个终结符a
                //nonEndChar -> rightItemSub加入M[nonEndChar,a]中
                else {
                    for (String a : rightFirst) {
                        table.put(Pair.of(nonEndChar, a), Pair.of(nonEndChar, rightItem));
                    }
                }

            }
        }
    }

    private static HashSet<String> get_right_first(String rightItem) {
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
     * this method is to read the standard input
     */
    private static void read_prog() {
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
     * you should add some code in this method to achieve this lab
     */

    /**
     * 使用递归下降的语法分析方法
     */

    private static void stack_pop(Deque<String> stack, Deque<Integer>indents, List<Map.Entry<String,Integer>> grammarTree){
        grammarTree.add(Pair.of(stack.peek(), indents.peek()));
        stack.pop();
        indents.pop();
    }
    private static void analysis() {
        Deque<String> stack = new ArrayDeque<>();
        Deque<Integer> indents = new ArrayDeque<>();
        stack.push("$");
        indents.push(0);
        stack.push(start);
        indents.push(0);
        String stackTop;
        String curInput;
        int indentTop = 0;
        Map.Entry<String,String> grammar;
        LinkedList<Map.Entry<String,Integer>> grammarTree = new LinkedList<>();
        int errorLine = 0;

        while(!stack.isEmpty() && !prog.isEmpty()){
            stackTop = stack.peek();
            indentTop = indents.peek();
            curInput = prog.get(0).getKey();
            grammar = table.get(Pair.of(stackTop,curInput));

            //X == a , 出栈
            if(stackTop.equals(curInput)){
                stack_pop(stack, indents, grammarTree);
                errorLine = prog.get(0).getValue();
                prog.remove(0);
//                System.out.println(curInput + "出栈");
            }
            else if(endChars.contains(stackTop)){
                if(stackTop.equals("E")){
                    stack_pop(stack, indents, grammarTree);
                    continue;
                }
                System.out.println("语法错误,第"+errorLine+"行,缺少"+"\""+stackTop+"\"");
                stack_pop(stack,indents,grammarTree);
            }
            else if(grammar != null){
                stack_pop(stack, indents, grammarTree);
                String[] Chars = grammar.getValue().split(" ");
                for(int i=Chars.length-1; i>=0;i--){
                    stack.push(Chars[i]);
                    indents.push(indentTop+1);
                }
//                System.out.println(stackTop+"->"+grammar.getValue());
            } else if (grammar == null) {
                stack_pop(stack,indents,grammarTree);
                stack.push("E");
                indents.push(indentTop+1);

            }

        }
//        print grammar tree
        for(Map.Entry<String,Integer> leaf:grammarTree){
            for(int i=0;i< leaf.getValue();i++){
                System.out.print("\t");
            }
            System.out.println(leaf.getKey());
        }

    }

    /**
     * this is the main method
     *
     * @param args
     */
    public static void main(String[] args) {
//        System.out.println("1");
        read_prog();
//        System.out.println("2");
        init_data();
//        System.out.println("3");
        analysis();
//        System.out.println("4");
    }
}

