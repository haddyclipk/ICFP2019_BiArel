# 1 "src/lexer.mll"
 
open Support.FileInfo
open Support.Error

let lex_error fi s = error_msg Support.Options.Lexer fi "%s" s

let reservedWords = [
  (* Symbols *)
  ("-", fun i -> Parser.DASH i);
  (";", fun i -> Parser.SEMI i);
  ("^", fun i -> Parser.HAT i);
  ("{", fun i -> Parser.LBRACE i);
  ("}", fun i -> Parser.RBRACE i);
  (":", fun i -> Parser.COLON i);
  ("::", fun i -> Parser.DBLCOLON i);
  (",", fun i -> Parser.COMMA i);
  ("<=", fun i -> Parser.LEQ i);
  ("=", fun i -> Parser.EQUAL i);
  ("->", fun i -> Parser.ARROW i);
  ("-->", fun i -> Parser.LARROW i);
  ("=>", fun i -> Parser.DBLARROW i);
  ("+", fun i -> Parser.ADD i);
  ("-", fun i -> Parser.SUB i);
  ("*", fun i -> Parser.MUL i);
  ("X", fun i -> Parser.TIMES i);
  ("/", fun i -> Parser.DIV i);
  ("(", fun i -> Parser.LPAREN i);
  (")", fun i -> Parser.RPAREN i);
  ("[", fun i -> Parser.LBRACK i);
  ("]", fun i -> Parser.RBRACK i);
  ("|", fun i -> Parser.PIPE i);
  ("&", fun i -> Parser.AMP i);
  ("||", fun i -> Parser.OR i);
  ("&&", fun i -> Parser.AND i);
  (".", fun i -> Parser.DOT i);

  
  (* Keywords *)
  ("true", fun i -> Parser.TRUE i);
  ("false", fun i -> Parser.FALSE i);
  ("unit", fun i -> Parser.UNIT i);
  ("unitR", fun i -> Parser.UNITR i);
  ("inf", fun i -> Parser.INF i);
  ("contra", fun i -> Parser.CONTRA i);
  ("fun", fun i -> Parser.FUN i);
  ("case", fun i -> Parser.UNIONCASE i);
  ("caseL", fun i -> Parser.LISTCASE i);
  ("at", fun i -> Parser.AT i);
  ("of", fun i -> Parser.OF i);
  ("inl", fun i -> Parser.INL i);
  ("inr", fun i -> Parser.INR i);
  ("fst", fun i -> Parser.FST i);
  ("snd", fun i -> Parser.SND i);
  ("as", fun i -> Parser.AS i);
  ("as", fun i -> Parser.AS i);
  ("nil", fun i -> Parser.NIL i);
  ("mu", fun i -> Parser.MU i);
  ("let", fun i -> Parser.LET i);
  ("clet", fun i -> Parser.CLET i);
  ("fix", fun i -> Parser.FIX i);
  ("Lam", fun i -> Parser.BIGLAMBDA i);
  ("lam", fun i -> Parser.LAMBDA i);
  ("primitive", fun i -> Parser.PRIMITIVE i);
  ("if", fun i -> Parser.IF i);
  ("then", fun i -> Parser.THEN i);
  ("else", fun i -> Parser.ELSE i);
  ("print", fun i -> Parser.PRINT i);
  ("bool", fun i -> Parser.BOOL i);
  ("boolR", fun i -> Parser.BOOLR i);
  ("num", fun i -> Parser.NUM i);
  ("list", fun i -> Parser.LIST i);
  ("type", fun i -> Parser.TYPE i);
  ("pack", fun i -> Parser.PACK i);
  ("with", fun i -> Parser.WITH i);
  ("size", fun i -> Parser.SIZE i);
  ("cost", fun i -> Parser.COST i);
  ("diff", fun i -> Parser.DIFF i);
  ("max", fun i -> Parser.MAX i);
  ("min", fun i -> Parser.MIN i);
  ("in", fun i -> Parser.IN i);
  ("fl", fun i -> Parser.FLOOR i);
  ("cl", fun i -> Parser.CEIL i);
  ("log", fun i -> Parser.LOG i);
  ("unpack", fun i -> Parser.UNPACK i);
  ("forall", fun i -> Parser.FORALL i);
  ("exists", fun i -> Parser.EXISTS i);
  ("minpowlin", fun i -> Parser.MINPOWLIN i);
  ("minpowcon", fun i -> Parser.MINPOWCONSTANT i);
  ("sum", fun i -> Parser.SUM i);
  ("nat", fun i -> Parser.NAT i);
  ("int", fun i -> Parser.INT i);
  ("intR", fun i -> Parser.INTR i);
  ("U", fun i -> Parser.UNREL i);
  ("Z", fun i -> Parser.ZERO i);
  ("S", fun i -> Parser.SUCC i);
  ("B", fun i -> Parser.BOX i);
  ("alloc", fun i -> Parser.ALLOC i);
  ("read", fun i -> Parser.READ i);
  ("update", fun i -> Parser.UPDATE i);
  ("return", fun i -> Parser.RETURN i);
  ("letm", fun i -> Parser.LETM i); 
  ("Uint", fun i -> Parser.UINT i);
  ("Bint", fun i -> Parser.BINT i);
  ("array", fun i -> Parser.ARRAY i);
  ("loc", fun i -> Parser.LOC i);
  ("celim", fun i -> Parser.CELIM i);
  ("io" , fun i -> Parser.IO i     );
  ("<", fun i -> Parser.LT i);
  ("Arr", fun i -> Parser.ARR i);
  ("Union", fun i -> Parser.UNION i);
  ("Intersect", fun i -> Parser.INTERSECT i);
  ("SetDiff", fun i -> Parser.SETDIFF i);
  ("CBETAIN", fun i -> Parser.CBETAIN i);
  ("SPLIT", fun i -> Parser.SPLIT i) ;
  ("WITH", fun i -> Parser.WITH i);
  ("FIXEXT", fun i -> Parser.FIXEXT i) ;
  ("ie", fun i -> Parser.IE i);
  ("CBETAEQ", fun i -> Parser.CBETAEQ i);
  ("SWITCH", fun i -> Parser.SWITCH i);
  ("BETAMIN", fun i -> Parser.BETAMIN i);
  ("INTMAX", fun i -> Parser.INTMAX i);
  ("INTMIN", fun i -> Parser.INTMIN i);
  ("CNOT", fun i -> Parser.CNOT i);
]

(* Support functions *)

type buildfun = info -> Parser.token
let (symbolTable : (string,buildfun) Hashtbl.t) = Hashtbl.create 1024
let _ =
  List.iter (fun (str,f) -> Hashtbl.add symbolTable str f) reservedWords

let createID i str =
  try (Hashtbl.find symbolTable str) i
  with _ -> Parser.ID {i=i;v=str}

let lineno   = ref 1
and depth    = ref 0
and start    = ref 0

and filename = ref ""
and startLex = ref dummyinfo

let create inFile stream =
  if not (Filename.is_implicit inFile) then filename := inFile
  else filename := Filename.concat (Sys.getcwd()) inFile;
  lineno := 1; start := 0; Lexing.from_channel stream

let newline lexbuf = incr lineno; start := (Lexing.lexeme_start lexbuf)

let info lexbuf =
  createInfo (!filename) (!lineno) (Lexing.lexeme_start lexbuf - !start)

let text = Lexing.lexeme

let stringBuffer = ref (Bytes.create 2048)
let stringEnd = ref 0

let resetStr () = stringEnd := 0

let addStr ch =
  let x = !stringEnd in
  let buffer = !stringBuffer
in
  if x = Bytes.length buffer then
    begin
      let newBuffer = Bytes.create (x*2) in
      Bytes.blit buffer 0 newBuffer 0 x;
      Bytes.set newBuffer x ch;
      stringBuffer := newBuffer;
      stringEnd := x+1
    end
  else
    begin
      Bytes.set buffer x ch;
      stringEnd := x+1
    end

let getStr () = Bytes.sub (!stringBuffer) 0 (!stringEnd)

let extractLineno yytext offset =
  int_of_string ( Bytes.to_string (Bytes.sub (Bytes.of_string yytext) offset (Bytes.length (Bytes.of_string yytext) - offset)) )

# 186 "src/lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\240\255\241\255\242\255\243\255\090\000\005\000\099\000\
    \006\000\070\000\102\000\093\000\135\000\197\000\151\000\004\000\
    \099\000\017\000\254\255\001\000\143\000\004\000\253\255\124\000\
    \252\255\017\001\038\000\027\001\039\000\049\000\126\000\037\001\
    \047\001\057\001\078\001\245\255\097\000\171\000\251\255\252\255\
    \253\255\115\000\121\000\255\255\254\255\133\000\255\255\156\000\
    \175\000\134\000\159\000\166\000\252\255\253\255\254\255\255\255\
    \128\001\249\255\088\001\251\255\252\255\253\255\254\255\255\255\
    \098\001\250\255";
  Lexing.lex_backtrk =
   "\255\255\255\255\255\255\255\255\255\255\011\000\012\000\011\000\
    \012\000\012\000\011\000\012\000\011\000\009\000\007\000\012\000\
    \012\000\012\000\255\255\015\000\000\000\255\255\255\255\004\000\
    \255\255\255\255\255\255\005\000\255\255\255\255\255\255\255\255\
    \006\000\255\255\008\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\003\000\003\000\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\006\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255";
  Lexing.lex_default =
   "\001\000\000\000\000\000\000\000\000\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\000\000\255\255\255\255\255\255\000\000\023\000\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\000\000\255\255\039\000\000\000\000\000\
    \000\000\255\255\255\255\000\000\000\000\255\255\000\000\048\000\
    \048\000\255\255\050\000\052\000\000\000\000\000\000\000\000\000\
    \057\000\000\000\255\255\000\000\000\000\000\000\000\000\000\000\
    \255\255\000\000";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\020\000\018\000\018\000\020\000\019\000\018\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \020\000\004\000\003\000\015\000\025\000\005\000\005\000\004\000\
    \004\000\004\000\017\000\005\000\004\000\010\000\004\000\016\000\
    \014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
    \014\000\014\000\012\000\004\000\011\000\009\000\004\000\004\000\
    \022\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\006\000\005\000\004\000\004\000\013\000\
    \005\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\008\000\007\000\004\000\005\000\005\000\
    \005\000\035\000\035\000\036\000\035\000\005\000\255\255\005\000\
    \005\000\005\000\035\000\005\000\005\000\024\000\005\000\028\000\
    \005\000\005\000\023\000\005\000\005\000\029\000\030\000\035\000\
    \020\000\018\000\035\000\020\000\021\000\005\000\031\000\035\000\
    \005\000\035\000\044\000\043\000\035\000\045\000\255\255\046\000\
    \050\000\255\255\000\000\000\000\005\000\005\000\000\000\020\000\
    \054\000\000\000\005\000\000\000\005\000\038\000\005\000\000\000\
    \000\000\255\255\005\000\000\000\000\000\000\000\255\255\005\000\
    \035\000\005\000\005\000\005\000\035\000\033\000\005\000\014\000\
    \014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
    \014\000\255\255\000\000\000\000\000\000\041\000\005\000\000\000\
    \005\000\035\000\042\000\000\000\000\000\000\000\000\000\005\000\
    \035\000\005\000\005\000\005\000\005\000\000\000\000\000\005\000\
    \000\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\000\000\
    \002\000\000\000\055\000\005\000\000\000\005\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \000\000\000\000\000\000\000\000\013\000\000\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \000\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\034\000\034\000\034\000\034\000\034\000\034\000\034\000\
    \034\000\034\000\034\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\026\000\034\000\034\000\
    \034\000\034\000\034\000\034\000\034\000\034\000\034\000\034\000\
    \064\000\064\000\064\000\064\000\064\000\064\000\064\000\064\000\
    \064\000\064\000\065\000\065\000\065\000\065\000\065\000\065\000\
    \065\000\065\000\065\000\065\000\255\255\000\000\000\000\255\255\
    \000\000\000\000\060\000\000\000\000\000\000\000\053\000\059\000\
    \000\000\000\000\000\000\040\000\000\000\000\000\000\000\255\255\
    \058\000\058\000\058\000\058\000\058\000\058\000\058\000\058\000\
    \058\000\058\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\061\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\063\000\000\000\
    \000\000\000\000\000\000\000\000\062\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \255\255";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\019\000\000\000\000\000\021\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\015\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \017\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000\
    \005\000\006\000\008\000\009\000\009\000\005\000\023\000\005\000\
    \007\000\007\000\011\000\010\000\010\000\016\000\007\000\026\000\
    \007\000\010\000\016\000\010\000\005\000\028\000\029\000\011\000\
    \020\000\020\000\011\000\020\000\020\000\007\000\030\000\036\000\
    \010\000\007\000\041\000\042\000\010\000\045\000\047\000\045\000\
    \049\000\050\000\255\255\255\255\012\000\012\000\255\255\020\000\
    \051\000\255\255\012\000\255\255\012\000\037\000\005\000\255\255\
    \255\255\048\000\005\000\255\255\255\255\255\255\047\000\007\000\
    \007\000\012\000\010\000\007\000\012\000\014\000\010\000\014\000\
    \014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
    \014\000\048\000\255\255\255\255\255\255\037\000\005\000\255\255\
    \005\000\011\000\037\000\255\255\255\255\255\255\255\255\007\000\
    \007\000\007\000\010\000\012\000\010\000\255\255\255\255\012\000\
    \255\255\255\255\255\255\255\255\013\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\255\255\
    \000\000\255\255\051\000\012\000\255\255\012\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \255\255\255\255\255\255\255\255\013\000\255\255\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \255\255\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\027\000\027\000\027\000\027\000\027\000\
    \027\000\027\000\027\000\027\000\027\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\032\000\
    \032\000\032\000\032\000\032\000\032\000\032\000\032\000\032\000\
    \032\000\033\000\033\000\033\000\033\000\033\000\033\000\033\000\
    \033\000\033\000\033\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\023\000\025\000\034\000\034\000\
    \034\000\034\000\034\000\034\000\034\000\034\000\034\000\034\000\
    \058\000\058\000\058\000\058\000\058\000\058\000\058\000\058\000\
    \058\000\058\000\064\000\064\000\064\000\064\000\064\000\064\000\
    \064\000\064\000\064\000\064\000\047\000\255\255\255\255\050\000\
    \255\255\255\255\056\000\255\255\255\255\255\255\051\000\056\000\
    \255\255\255\255\255\255\037\000\255\255\255\255\255\255\048\000\
    \056\000\056\000\056\000\056\000\056\000\056\000\056\000\056\000\
    \056\000\056\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\056\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\056\000\255\255\
    \255\255\255\255\255\255\255\255\056\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \056\000";
  Lexing.lex_base_code =
   "";
  Lexing.lex_backtrk_code =
   "";
  Lexing.lex_default_code =
   "";
  Lexing.lex_trans_code =
   "";
  Lexing.lex_check_code =
   "";
  Lexing.lex_code =
   "";
}

let rec main lexbuf =
   __ocaml_lex_main_rec lexbuf 0
and __ocaml_lex_main_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 189 "src/lexer.mll"
                           ( main lexbuf )
# 403 "src/lexer.ml"

  | 1 ->
# 191 "src/lexer.mll"
                                  ( newline lexbuf; main lexbuf )
# 408 "src/lexer.ml"

  | 2 ->
# 193 "src/lexer.mll"
       ( lex_error (info lexbuf) "Unmatched end of comment" )
# 413 "src/lexer.ml"

  | 3 ->
# 195 "src/lexer.mll"
       ( depth := 1; startLex := info lexbuf; comment lexbuf; main lexbuf )
# 418 "src/lexer.ml"

  | 4 ->
# 197 "src/lexer.mll"
                 ( main lexbuf )
# 423 "src/lexer.ml"

  | 5 ->
# 200 "src/lexer.mll"
    ( lineno := extractLineno (text lexbuf) 2 - 1; getFile lexbuf )
# 428 "src/lexer.ml"

  | 6 ->
# 203 "src/lexer.mll"
    ( lineno := extractLineno (text lexbuf) 7 - 1; getFile lexbuf )
# 433 "src/lexer.ml"

  | 7 ->
# 206 "src/lexer.mll"
    ( Parser.INTV{i=info lexbuf; v=int_of_string (text lexbuf)} )
# 438 "src/lexer.ml"

  | 8 ->
# 209 "src/lexer.mll"
    ( Parser.FLOATV{i=info lexbuf; v=float_of_string (text lexbuf)} )
# 443 "src/lexer.ml"

  | 9 ->
# 213 "src/lexer.mll"
    ( createID (info lexbuf) (text lexbuf) )
# 448 "src/lexer.ml"

  | 10 ->
# 217 "src/lexer.mll"
    ( createID (info lexbuf) (text lexbuf) )
# 453 "src/lexer.ml"

  | 11 ->
# 220 "src/lexer.mll"
    ( createID (info lexbuf) (text lexbuf) )
# 458 "src/lexer.ml"

  | 12 ->
# 224 "src/lexer.mll"
    ( createID (info lexbuf) (text lexbuf) )
# 463 "src/lexer.ml"

  | 13 ->
# 226 "src/lexer.mll"
       ( resetStr(); startLex := info lexbuf; string lexbuf )
# 468 "src/lexer.ml"

  | 14 ->
# 228 "src/lexer.mll"
      ( Parser.EOF(info lexbuf) )
# 473 "src/lexer.ml"

  | 15 ->
# 230 "src/lexer.mll"
     ( lex_error (info lexbuf) "Illegal character" )
# 478 "src/lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_main_rec lexbuf __ocaml_lex_state

and comment lexbuf =
   __ocaml_lex_comment_rec lexbuf 37
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 234 "src/lexer.mll"
    ( depth := succ !depth; comment lexbuf )
# 490 "src/lexer.ml"

  | 1 ->
# 236 "src/lexer.mll"
    ( depth := pred !depth; if !depth > 0 then comment lexbuf )
# 495 "src/lexer.ml"

  | 2 ->
# 238 "src/lexer.mll"
    ( lex_error (!startLex) "Comment not terminated" )
# 500 "src/lexer.ml"

  | 3 ->
# 240 "src/lexer.mll"
    ( comment lexbuf )
# 505 "src/lexer.ml"

  | 4 ->
# 242 "src/lexer.mll"
    ( newline lexbuf; comment lexbuf )
# 510 "src/lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

and getFile lexbuf =
   __ocaml_lex_getFile_rec lexbuf 45
and __ocaml_lex_getFile_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 245 "src/lexer.mll"
            ( getName lexbuf )
# 522 "src/lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_getFile_rec lexbuf __ocaml_lex_state

and getName lexbuf =
   __ocaml_lex_getName_rec lexbuf 47
and __ocaml_lex_getName_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 248 "src/lexer.mll"
                ( filename := (text lexbuf); finishName lexbuf )
# 534 "src/lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_getName_rec lexbuf __ocaml_lex_state

and finishName lexbuf =
   __ocaml_lex_finishName_rec lexbuf 49
and __ocaml_lex_finishName_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 251 "src/lexer.mll"
                ( main lexbuf )
# 546 "src/lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_finishName_rec lexbuf __ocaml_lex_state

and string lexbuf =
   __ocaml_lex_string_rec lexbuf 51
and __ocaml_lex_string_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 254 "src/lexer.mll"
      ( addStr(escaped lexbuf); string lexbuf )
# 558 "src/lexer.ml"

  | 1 ->
# 255 "src/lexer.mll"
       ( addStr '\n'; newline lexbuf; string lexbuf )
# 563 "src/lexer.ml"

  | 2 ->
# 256 "src/lexer.mll"
       ( lex_error (!startLex) "String not terminated" )
# 568 "src/lexer.ml"

  | 3 ->
# 257 "src/lexer.mll"
       ( addStr (Lexing.lexeme_char lexbuf 0); string lexbuf )
# 573 "src/lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_string_rec lexbuf __ocaml_lex_state

and escaped lexbuf =
   __ocaml_lex_escaped_rec lexbuf 56
and __ocaml_lex_escaped_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 260 "src/lexer.mll"
       ( '\n' )
# 585 "src/lexer.ml"

  | 1 ->
# 261 "src/lexer.mll"
       ( '\t' )
# 590 "src/lexer.ml"

  | 2 ->
# 262 "src/lexer.mll"
        ( '\\' )
# 595 "src/lexer.ml"

  | 3 ->
# 263 "src/lexer.mll"
         ( '\034'  )
# 600 "src/lexer.ml"

  | 4 ->
# 264 "src/lexer.mll"
        ( '\'' )
# 605 "src/lexer.ml"

  | 5 ->
# 266 "src/lexer.mll"
    (
      let x = int_of_string(text lexbuf) in
      if x > 255 then
	lex_error (info lexbuf) "Illegal character constant"
      else
	Char.chr x
    )
# 616 "src/lexer.ml"

  | 6 ->
# 274 "src/lexer.mll"
    ( lex_error (info lexbuf) "Illegal character constant" )
# 621 "src/lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_escaped_rec lexbuf __ocaml_lex_state

;;

