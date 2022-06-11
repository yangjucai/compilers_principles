import java.util.HashMap;
import java.util.LinkedList;
import java.util.Scanner;

public class Java_LexAnalysis
{
//    private static StringBuffer prog = new StringBuffer();
    private static LinkedList<Character> list1 = new LinkedList<Character>();
    private static LinkedList<Character> list2 = new LinkedList<Character>();
    private static int state = 0;
    private static Token token = new Token();
    static IDType idType = new IDType();


    private static class Token{
        private String name;
        private int id;
        private int cnt = 1;

        @Override
        public String toString() {
            return cnt + ": <" + this.name + "," +this.id + ">";
        }

        public void display() {
            System.out.println(this.cnt + ": <" + this.name +"," + this.id +  ">");
            this.cnt += 1;
        }

        public void setName(String name) {
            this.name = name;
        }

        public void setId(int id) {
            this.id = id;
        }
    }

    private static class IDType{
        public static HashMap<String, Integer> keywords = new HashMap<String, Integer>();
        public IDType() {
            keywords.put("auto",1);
            keywords.put("break",2);
            keywords.put("case",3);
            keywords.put("char",4);
            keywords.put("const",5);
            keywords.put("continue",6);
            keywords.put("default",7);
            keywords.put("do",8);
            keywords.put("double",9);
            keywords.put("else",10);
            keywords.put("enum",11);
            keywords.put("extern",12);
            keywords.put("float",13);
            keywords.put("for",14);
            keywords.put("goto",15);
            keywords.put("if",16);
            keywords.put("int",17);
            keywords.put("long",18);
            keywords.put("register",19);
            keywords.put("return",20);
            keywords.put("short",21);
            keywords.put("signed",22);
            keywords.put("sizeof",23);
            keywords.put("static",24);
            keywords.put("struct",25);
            keywords.put("switch",26);
            keywords.put("typedef",27);
            keywords.put("union",28);
            keywords.put("unsigned",29);
            keywords.put("void",30);
            keywords.put("volatile",31);
            keywords.put("while",32);
        }
    }




    /**
     *  this method is to read the standard input
     */
    private static void read_prog()
    {
        Scanner sc = new Scanner(System.in);
        char char_arr[];
        while(sc.hasNextLine())
        {
            String tmp = sc.nextLine();
            tmp.replaceAll("\\s+", "");
            char_arr = tmp.toCharArray();
            for (char _char : char_arr) {
                list1.offer(_char);
            }
            list1.offer('\n');
        }
    }


    // add your method here!!

    static char readin() {              //读入操作：取出list1的第一个字符放入list2的末尾
        char a1 = list1.pollFirst();
        list2.offerLast(a1);
        return a1;
    }

    static void readout() {            //读出操作；取出list2的最后一个字符放回list1
        char a2 = list2.pollLast();
        list1.offerFirst(a2);
    }

    static  String getFromList2() {       //过去list2里的内容以供输出
        String string = new String();
        for (int i = 0; i < list2.size(); i++) {
            char _char = list2.get(i);
            string += _char;
        }
        return string;
    }

    private static void setToken(String name, int id){
        token.setName(name);
        token.setId(id);
        token.display();
        state = 0;
        list2.clear();
    }


    /**
     *  you should add some code in this method to achieve this lab
     */
    private static void analysis()
    {
        read_prog();
        state = 0;

        while (!list1.isEmpty()) {
            char c = readin();
            if(c == '\n')
                continue;
            switch (state) {
                case 0:
                    if (c == ' ') continue;
                    else if (Character.isLetter(c))
                        state = 1;
                    else if (Character.isDigit(c))
                        state = 3;
                    else if (c == '+')
                        state = 10;
                    else if (c == '-')
                        state = 14;
                    else if (c == '*')
                        state = 18;
                    else if (c == '/')
                        state = 21;
                    else if (c == '%')
                        state = 24;
                    else if (c == '&')
                        state = 27;
                    else if (c == '|')
                        state = 31;
                    else if (c == '!')
                        state = 35;
                    else if (c == '^')
                        state = 38;
                    else if (c == '<')
                        state = 41;
                    else if (c == '>')
                        state = 47;
                    else if (c == '=')
                        state = 57;
                    else if (c == '?') {
                        state = 60;
                        readout();
                    } else if (c == ':') {
                        readout();
                        state = 61;
                    } else if (c == '[') {
                        state = 62;
                        readout();
                    } else if (c == ']') {
                        state = 63;
                        readout();
                    } else if (c == '(') {
                        state = 64;
                        readout();
                    } else if (c == ')') {
                        state = 65;
                        readout();
                    } else if (c == '.') {
                        state = 66;
                        readout();
                    } else if (c == ',') {
                        state = 67;
                        readout();
                    } else if (c == '{') {
                        state = 68;
                        readout();
                    } else if (c == '}') {
                        state = 69;
                        readout();
                    } else if (c == ';') {
                        state = 70;
                        readout();
                    } else if (c == '"') {
                        state = 71;
                        readout();
                    } else if (c == '~'){
                        state = 73;
                        readout();
                    }
                    else {
                        if (c != ' ') {
//                            System.out.print("不能识别");
                            list2.clear();
                            continue;
                        }
                    }
                    break;
                case 1:
                    if (Character.isLetter(c) || Character.isDigit(c))
                        state = 1;
                    else {
                        readout();
                        state = 2;
                    }
                    break;
                case 2: // 标识符或关键字类型
                    readout();
                    String string = getFromList2();
                    if (idType.keywords.containsKey(string.trim())) { // 如果能在关键字表中找到，则是关键字类型
                        token.setName(string.trim());
                        token.setId(idType.keywords.get(string.trim()));
                    } else { // 否则，是标识符类型
                        token.setName(string.trim());
                        token.setId(81);
                    }
                    token.display();
                    list2.clear();
                    state = 0;
                    break;
                case 3:
                    if (Character.isDigit(c))
                        state = 3;
                    else if (c == '.')
                        state = 4;
                    else if (c == 'e' || c == 'E')
                        state = 6;
                    else {
                        state = 9;
                        readout();
                    }
                    break;
                case 4:
                    if (Character.isDigit(c))
                        state = 5;
                    else {
                        if (c != ' ') {
//                            System.out.print("不能识别");
                            list2.clear();
                            continue;
                        }
                    }
                    break;
                case 5:
                    if (c == 'e' || c == 'E')
                        state = 6;
                    else {
                        state = 9;
                        readout();
                    }
                    break;
                case 6:
                    if (c == '+' || c == '-')
                        state = 7;
                    else if (Character.isDigit(c))
                        state = 8;
                    else {
                        if (c != ' ') {
//                            System.out.print("不能识别");
                            list2.clear();
                            continue;
                        }
                    }
                    break;
                case 7:
                    if (Character.isDigit(c))
                        state = 8;
                    else {
//                        System.out.print("不能识别");
                        list2.clear();
                        continue;
                    }
                    break;
                case 8:
                    if (Character.isDigit(c))
                        state = 8;
                    else {
                        state = 9;
                        readout();
                    }
                    break;
                case 9: // 数值类型
                    readout();
                    String string1 = getFromList2();
                    token.setName(string1.trim());
                    token.setId(80);
                    token.display();

                    list2.clear();
                    state = 0;
                    break;
                case 10:
                    if (Character.isDigit(c))
                        state = 3;
                    else if (c == '+') {
                        state = 11;
                        readout();
                    } else if (c == '=') {
                        state = 12;
                        readout();
                    } else {
                        state = 13;
                        readout();
                    }
                    break;
                case 11: // ++
                    setToken(getFromList2().trim(),66);
                    break;
                case 12: // +=
                    setToken(getFromList2().trim(),67);
                    break;
                case 13: // +
                    readout();
                    setToken(getFromList2().trim(),65);
                    break;
                case 14:
                    if (Character.isDigit(c))
                        state = 3;
                    else if (c == '-') {
                        state = 15;
                        readout();
                    } else if (c == '=') {
                        state = 16;
                        readout();
                    } else if (c == '>'){
                        state = 72;
                        readout();
                    }
                    else {
                        state = 17;
                        readout();
                    }
                    break;
                case 15: // --
                    setToken(getFromList2().trim(),34);
                    break;
                case 16: // -=
                    setToken(getFromList2().trim(),35);
                    break;
                case 17: // -
                    readout();
                    setToken(getFromList2().trim(),33);
                    break;
                case 18:
                    if (c == '*') {
                        state = 19;
                        readout();
                    } else {
                        state = 20;
                        readout();
                    }
                    break;
                case 19: // *=
                    setToken(getFromList2().trim(),47);
                    break;
                case 20: // *
                    readout();
                    setToken(getFromList2().trim(),46);
                    break;
                case 21:
                    if (c == '=') {
                        state = 22;
                        readout();
                    } else if (c == '*'){
                        state = 74;
                        readout();
                    } else if (c == '/'){
                        state = 75;
                        readout();
                    } else {
                        state = 23;
                        readout();
                    }
                    break;
                case 22: // /=
                    setToken(getFromList2().trim(),51);
                    break;
                case 23: // /
                    readout();
                    setToken(getFromList2().trim(),50);
                    break;
                case 24:
                    if (c == '=') {
                        state = 25;
                        readout();
                    } else if(Character.isLetter(c)) {
                        state = 1;//%d
                        readout();
                    } else {
                        state = 26;
                        readout();
                    }
                    break;
                case 25: // %=
                    setToken(getFromList2().trim(),40);
                    break;
                case 26: // %
                    readout();
                    setToken(getFromList2().trim(),39);
                    break;
                case 27:
                    if (c == '&') {
                        state = 28;
                        readout();
                    } else if (c == '=') {
                        state = 29;
                        readout();
                    } else {
                        state = 30;
                        readout();
                    }
                    break;
                case 28: // &&
                    setToken(getFromList2().trim(),42);
                    break;
                case 29: // &=
                    setToken(getFromList2().trim(),43);
                    break;
                case 30: // &
                    readout();
                    setToken(getFromList2().trim(),41);
                    break;
                case 31:
                    if (c == '|') {
                        state = 32;
                        readout();
                    } else if (c == '=') {
                        state = 33;
                        readout();
                    } else {
                        state = 34;
                        readout();
                    }
                    break;
                case 32: // ||
                    setToken(getFromList2().trim(),61);
                    break;
                case 33: // |=
                    setToken(getFromList2().trim(),62);
                    break;
                case 34: // |
                    readout();
                    setToken(getFromList2().trim(),60);
                    break;
                case 35:
                    if (c == '=') {
                        state = 36;
                        readout();
                    } else {
                        state = 37;
                        readout();
                    }
                    break;
                case 36: // !=
                    setToken(getFromList2().trim(),38);
                    break;
                case 37: // !
                    readout();
                    setToken(getFromList2().trim(),37);
                    break;
                case 38:
                    if (c == '=') {
                        state = 39;
                        readout();
                    } else {
                        state = 40;
                        readout();
                    }
                    break;
                case 39: // ^=
                    setToken(getFromList2().trim(),58);
                    break;
                case 40: // ^
                    readout();
                    setToken(getFromList2().trim(),57);
                    break;
                case 41:
                    if (c == '=') {
                        state = 42;
                        readout();
                    } else if (c == '<') {
                        state = 43;
                    } else {
                        state = 46;
                        readout();
                    }
                    break;
                case 42: // <=
                    setToken(getFromList2().trim(),71);
                    break;
                case 43:
                    if (c == '=') {
                        state = 44;
                        readout();
                    } else {
                        state = 45;
                        readout();
                    }
                    break;
                case 44: // <<=
                    setToken(getFromList2().trim(),70);
                    break;
                case 45: // <<
                    readout();
                    setToken(getFromList2().trim(),69);
                    break;
                case 46: // <
                    readout();
                    setToken(getFromList2().trim(),68);
                    break;
                case 47:
                    if (c == '=') {
                        state = 48;
                        readout();
                    } else if (c == '>')
                        state = 49;
                    else {
                        state = 55;
                        readout();
                    }
                    break;
                case 48: // >=
                    setToken(getFromList2().trim(),75);
                    break;
                case 49:
                    if (c == '>')
                        state = 50;
                    else if (c == '=') {
                        state = 53;
                        readout();
                    } else {
                        state = 54;
                        readout();
                    }
                    break;
                case 50:
                    if (c == '=') {
                        state = 51;
                        readout();
                    } else {
                        state = 52;
                        readout();
                    }
                    break;
                case 51: // >>>=
                    setToken(getFromList2().trim(),101);
                    break;
                case 52: // >>>
                    readout();
                    setToken(getFromList2().trim(),100);
                    break;

                case 53: // >>=
                    setToken(getFromList2().trim(),77);
                    break;
                case 54: // >>
                    readout();
                    setToken(getFromList2().trim(),76);
                    break;
                case 55: // >
                    readout();
                    setToken(getFromList2().trim(),74);
                    break;
                case 56:
                    break;
                case 57:
                    if (c == '=') {
                        state = 58;
                        readout();
                    } else {
                        state = 59;
                        readout();
                    }
                    break;
                case 58: // ==
                    setToken(getFromList2().trim(),73);
                    break;
                case 59: // =
                    readout();
                    setToken(getFromList2().trim(),72);
                    break;
                case 60: // ?
                    setToken(getFromList2().trim(),54);
                    break;
                case 61: // :
                    setToken(getFromList2().trim(),52);
                    break;
                case 62: // [
                    setToken(getFromList2().trim(),55);
                    break;
                case 63: // ]
                    setToken(getFromList2().trim(),56);
                    break;
                case 64: // (
                    setToken(getFromList2().trim(),44);
                    break;
                case 65: // )
                    setToken(getFromList2().trim(),45);
                    break;
                case 66: // .
                    setToken(getFromList2().trim(),49);
                    break;
                case 67: // ,
                    setToken(getFromList2().trim(),48);
                    break;
                case 68: // {
                    setToken(getFromList2().trim(),59);
                    break;
                case 69: // }
                    setToken(getFromList2().trim(),63);
                    break;
                case 70: // ;
                    setToken(getFromList2().trim(),53);
                    break;
                case 71: // "
                    setToken(getFromList2().trim(),78);
                    break;
                case 72: // ->
                    setToken(getFromList2().trim(),36);
                    break;
                case 73: // ~
                    setToken(getFromList2().trim(),64);
                    break;
                case 74: // /* */
                    String annotation_mul_line = "";
                    Character cur_char = readin();
                    while(true){
                        if(cur_char == '*'){
                            cur_char = readin();
                            if(cur_char == '/'){
                                break;
                            }
                        }
                        cur_char = readin();
                    }
                    annotation_mul_line += getFromList2().trim();
                    token.setName(annotation_mul_line);
                    token.setId(79);
                    token.display();
                    state = 0;
                    list2.clear();
                    break;
                case 75:// //
                    String annotation_sig_line = "";
                    Character cur_char1 = readin();
                    while(true){
                        if(cur_char1 == '\n')
                            break;
                        cur_char1 = readin();

                    }
                    list2.pollLast();
                    annotation_sig_line += getFromList2().trim();
                    token.setName(annotation_sig_line);
                    token.setId(79);
                    token.display();
                    state = 0;
                    list2.clear();
                    break;
                case 76:// %d
                    setToken(getFromList2().trim(),81);
                    break;

            }
        }

    }

    /**
     * this is the main method
     * @param args
     */
    public static void main(String[] args) {
        analysis();
    }
}
