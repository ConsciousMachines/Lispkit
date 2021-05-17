using System;
using System.Text;

namespace Lispkit
{
    public static class T // tools
    {
        public static void assert(bool b, string m = "") { if (!b) throw new Exception(m); }
    }
    public static class secd
    {
        public static data s, e, c, d;
        public static data t, f, nil, w;
        private static bool should_continue = true;
        private static void LDC()
        {
            s = data.newCons(c.cdr.car, s);
            c = c.cdr.cdr;
        }
        private static void LD()
        {
            w = e;
            for (int i = 1; i <= c.cdr.car.car.n; i++) w = w.cdr; // p 307 
            w = w.car;
            for (int i = 1; i <= c.cdr.car.cdr.n; i++) w = w.cdr;
            w = w.car;
            s = data.newCons(w, s);
            c = c.cdr.cdr;
        }
        private static void CAR()
        {
            s = data.newCons(s.car.car, s.cdr);
            c = c.cdr;
        }
        private static void CDR()
        {
            s = data.newCons(s.car.cdr, s.cdr);
            c = c.cdr;
        }
        private static void ATOM()
        {
            if (s.car.isnumber || s.car.issymbol) s = data.newCons(t, s.cdr);
            else s = data.newCons(f, s.cdr);
            c = c.cdr;
        }
        private static void CONS()
        {
            s = data.newCons(data.newCons(s.car, s.cdr.car), s.cdr.cdr);
            c = c.cdr;
        }
        private static void SUB()
        {
            s = data.newCons(data.newNum(s.cdr.car.n - s.car.n), s.cdr.cdr);
            c = c.cdr;
        }
        private static void ADD()
        {
            s = data.newCons(data.newNum(s.cdr.car.n + s.car.n), s.cdr.cdr);
            c = c.cdr;
        }
        private static void MUL()
        {
            s = data.newCons(data.newNum(s.cdr.car.n * s.car.n), s.cdr.cdr);
            c = c.cdr;
        }
        private static void DIV()
        {
            s = data.newCons(data.newNum(s.cdr.car.n / s.car.n), s.cdr.cdr);
            c = c.cdr;
        }
        private static void REM()
        {
            s = data.newCons(data.newNum(s.cdr.car.n % s.car.n), s.cdr.cdr);
            c = c.cdr;
        }
        private static void LEQ()
        {
            if (s.cdr.car.n <= s.car.n) s = data.newCons(t, s.cdr.cdr);
            else s = data.newCons(f, s.cdr.cdr);
            c = c.cdr;
        }
        private static void EQ()
        {
            if ((s.car.issymbol && s.cdr.car.issymbol && (s.car.s == s.cdr.car.s)) ||
                (s.car.isnumber && s.cdr.car.isnumber && (s.car.n == s.cdr.car.n)))
            {
                s = data.newCons(t, s.cdr.cdr);
            }
            else s = data.newCons(f, s.cdr.cdr);
            c = c.cdr;
        }
        private static void LDF()
        {
            s = data.newCons(data.newCons(c.cdr.car, e), s);
            c = c.cdr.cdr;
        }
        private static void AP()
        {
            d = data.newCons(s.cdr.cdr, data.newCons(e, data.newCons(c.cdr, d)));
            e = data.newCons(s.cdr.car, s.car.cdr);
            c = s.car.car;
            s = nil;
        }
        private static void RTN()
        {
            s = data.newCons(s.car, d.car);
            e = d.cdr.car;
            c = d.cdr.cdr.car;
            d = d.cdr.cdr.cdr;
        }
        private static void DUM()
        {
            e = data.newCons(nil, e);
            c = c.cdr;
        }
        private static void RAP()
        {
            d = data.newCons(s.cdr.cdr, data.newCons(e.cdr, data.newCons(c.cdr, d)));
            e = s.car.cdr;
            e.car = s.cdr.car;
            c = s.car.car;
            s = nil;
        }
        private static void SEL()
        {
            d = data.newCons(c.cdr.cdr.cdr, d);
            if (s.car.s == "T") c = c.cdr.car;
            else c = c.cdr.cdr.car;
            s = s.cdr;
        }
        private static void JOIN()
        {
            c = d.car;
            d = d.cdr;
        }
        private static void STOP() => should_continue = false;
        public static data exec(data fn, data args)
        {
            t = data.newSymbol("T");
            f = data.newSymbol("F");
            nil = data.NIL;

            s = data.newCons(args, nil);
            e = nil;
            c = fn;
            d = nil;

            // cycle 
            while (should_continue)
            {
                T.assert(c.car.t == data.type.NUMBER, "INVALID TYPE WHERE BYTECODE SHOULD BE");
                int op_code = c.car.n;
                switch (op_code)
                {
                    case 1: LD(); break;
                    case 2: LDC(); break;
                    case 3: LDF(); break;
                    case 4: AP(); break;
                    case 5: RTN(); break;
                    case 6: DUM(); break;
                    case 7: RAP(); break;
                    case 8: SEL(); break;
                    case 9: JOIN(); break;
                    case 10: CAR(); break;
                    case 11: CDR(); break;
                    case 12: ATOM(); break;
                    case 13: CONS(); break;
                    case 14: EQ(); break;
                    case 15: ADD(); break;
                    case 16: SUB(); break;
                    case 17: MUL(); break;
                    case 18: DIV(); break;
                    case 19: REM(); break;
                    case 20: LEQ(); break;
                    case 21: STOP(); break;
                    default: throw new Exception("not implemented code?");
                }
            }

            // end cycle
            return s.car;
        }
    }
    public static class lexer
    {
        static private string text;
        static private int i; // positions in the string 
        static private bool is_whitespace(char c) => " \t\n\r".Contains(c);
        // Numeric 48 -> 57 Capitals 65 -> 90 Lowers 97 -> 122 Underscore
        static private bool is_alphanumeric(char c) => (!((c < 48) || (c > 57 && c < 65) || (c > 90 && c < 97) || (c > 122)) || (c == '_'));
        // look at the current char
        static private char curr_char() => (i < text.Length) ? text[i] : '$';
        // advance the stream by 1 char, and view it 
        static private char next_char() { i++; return curr_char(); }
        // eat one char like pacman, then get next_char
        static private char consume_char(char c) { T.assert(text[i] == c, $"expected [{c}], got [{text[i]}]"); return next_char(); }
        // eat up whitespace 
        static private void consume_whitespace() { while (is_whitespace(curr_char())) i++; }

        // parse a variable name which may contain numbers
        static private string parse_symbol()
        {
            // align the 2 pointers
            int j = i;
            // move j forward while there are alphanumeric chars
            while ((j < text.Length) && is_alphanumeric(text[j])) j++;
            // between i and j is our alphanumeric identifier
            string ret = text.Substring(i, j - i);
            // advance i, should now be at the first non-alphanumeric char
            i = j;
            return ret;
        }

        public static data parse_S_expr_list()
        {
            if (curr_char() == ')') return data.NIL; // the expr is () -> empty list 

            data first = parse_S_expr(); // parse whatever the first thing is
            consume_whitespace();

            // <S-expr-list> ::== <S-expr>.<S-expr>
            if (curr_char() == '.') 
            {
                consume_char('.');
                data second = parse_S_expr();
                consume_whitespace(); // next token is )
                // if (A.B) and B is a CONS, proceed as usual
                if (second.t == data.type.CONS) return data.newCons(first, second);
                
                // if (A.B) and B is an ATOM, wrap it in a CONS cell with NIL cdr. 
                else return data.newCons(first, data.newCons(second, data.NIL));
            }

            // <S-expr-list> ::== <S-expr> <S-expr-list>
            data cdr = parse_S_expr_list(); // parse whatever the rest is -> tail or NIL
            return data.newCons(first, cdr);
        }
        public static data parse_S_expr() // pares atom or s-expr-list 
        {
            consume_whitespace();

            if (is_alphanumeric(curr_char())) // parse atom
            {
                string _data = parse_symbol(); // get the lexeme
                int resn;
                if (int.TryParse(_data, out resn)) return data.newNum(resn); // if its a number, return NUMBER
                else return data.newSymbol(_data); // else return SYMBOL
            }
            else if (curr_char() == '(') // parse s-expr-list
            {
                consume_char('(');
                data res = parse_S_expr_list();
                consume_char(')');
                return res;
            }
            else { throw new Exception("unexpected char?"); }
        }
        public static void lex(string input)
        {
            text = input;
            data rez = parse_S_expr();
            Console.WriteLine(rez);

            i = 0;
            text = "( LAMBDA ( X ) (MUL X X) )";
            data function = parse_S_expr();
            Console.WriteLine(function);

            data compiled = secd.exec(rez, data.newCons(function, data.NIL));
            Console.WriteLine(compiled);

        }
    }
    public class data
    {
        public string print(int depth = 0, bool head = true)
        {
            // if the CAR of a CONS cell is a CONS cell, it's a new head list
            switch(this.t)
            {
                case (type.NUMBER): return this.n.ToString();
                case (type.SYMBOL): return this.s == "NIL" ? "" : this.s;
                case (type.CONS):
                    {
                        StringBuilder ret = new StringBuilder();
                        if (head) ret.Append($"\n{new String(' ', depth)}( ");
                        if (this.car.t == type.CONS) ret.Append(this.car.print(depth + 2, true));
                        else ret.Append(this.car.print(depth + 2, false));
                        ret.Append(" ");
                        ret.Append(this.cdr.print(depth, false));
                        if (head) ret.Append(")"); // not adding space bc NIL is empty string, separated by space
                        return ret.ToString();
                    }
            }
            throw new Exception();
        }
        public override string ToString() => this.print(0);
        public bool issymbol => this.t == type.SYMBOL;
        public bool isnumber => this.t == type.NUMBER;
        public bool iscons => this.t == type.CONS;

        public enum type { SYMBOL, NUMBER, CONS};
        public readonly type t;
        public readonly string s;
        public readonly int n;
        public data car;
        public data cdr;
        private data(type t, string s, int n, data car, data cdr) { this.t = t; this.s = s; this.n = n; this.car = car; this.cdr = cdr; }
        static public data newSymbol(string s) => new data(type.SYMBOL, s, 0, null, null);
        static public data newNum(int n) => new data(type.NUMBER, null, n, null, null);
        static public data newCons(data f, data s) => new data(type.CONS, null, 0, f, s);
        readonly public static data NIL = newSymbol("NIL");

    }
    class Program
    {
        static void Main(string[] args)
        {
            string file = @"C:\Users\pwnag\source\repos\Lispkit\Lispkit\soy.lisp";
            string input = System.IO.File.ReadAllText(file, System.Text.Encoding.ASCII);
            lexer.lex(input);

            Console.WriteLine("Hello World!");
        }
    }
}
