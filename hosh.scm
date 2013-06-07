#!/usr/local/bin/gosh
(define %op (apply hash-table '(eq?
  (|.| l 19) (o a 19)
  (^ r 18) (* a 17) (/ a 17) (% l 17) (+ a 16) (- a 16)
  (& a 15) (|::| r 15) (++ r 15) (.. r 15)
  (== l 14) (!= l 14) (< a 14) (<= a 14) (> a 14) (>= a 14) (=~ l 14) (!~ l 14)
  (&& a 13) (|\|\|| a 12)
  (<$> r 9) ($ r 9) ($@ r 9) (? r 8) (then r 8) (|:| a 7) (else a 7)
  (of l 6) (in r 6) (where l 6) (catch r 6)
  (-> a 5) (|\|| a 4) (<- r 3) (= r 3) (|:=| a 3) (|,| a 2) (|;| a 2) ($$ r 2)
  (|(| l 1) (|)| l 1) (|{| l 1) (|}| l 1) (|[| l 1) (|]| l 1))))
(define-syntax uses (syntax-rules () ((_   m   ...) (begin (use m) ...))))
(define-syntax defs (syntax-rules () ((_ (k v) ...) (begin (define k v) ...))))
(define-syntax macs (syntax-rules () ((_ (k v) ...) (begin (define-macro (k . x) `(v ,@x)) ...))))
(uses util.match)
(defs (True #t) (False #f) (|::| cons) (++ append) (== equal?) (^ expt) (% modulo) ($@ apply) (! not) (o compose) (<$> map))
(macs (<- set!) (then and) (? and) (&& and) (|\|\|| or) (|;| begin))
(define-method object-apply (obj key) (guard (e (else #f)) (ref obj key)))
(define-method (setter object-apply) (obj key val) (set! (ref obj key) val) obj)

(define (=p x) (memq x '(= |:=|)))
(define (%np? x) (not (memq x '(|::| list))))
(define (%where xs) (match xs
  (() ())
  ((('= ('apply f ()) b) . xs) `((= ,f (-> '() ,b)) ,@(%where xs)))
  ((((? =p o) ((? %np? f) . a) b) . xs) (let
    ((c `(-> ,(if (eq? o '=) a `(_ ,@a)) ,b))
     (f? (pa$ eq? f))) (match (%where xs)
    ((((? =p) (? f?) ('|\|| . ps)) . xs) `((,o ,f (|\|| ,c ,@ps)) ,@xs))
    (                                xs  `((,o ,f (|\|| ,c     )) ,@xs)))))
  ((x . xs) `(,x ,@(%where xs)))
  (xs xs)))
(define (%unsemc x) (match x (('|;| . x) x) (x `(,x))))
(define (%onearg? x) (or (not (pair? x)) (memq (car x) '(|::| list))))
(define (%listm x) (if (%onearg? x) `(,x) x))
(define (%mkpat x) (match x
  ('True #t)
  ('False #f)
  (('|::| x y) (cons (%mkpat x) (%mkpat y)))
  (('list . xs) (map %mkpat xs))
  (('-> x y) `(,(%listm (%mkpat x)) ,y))
  (('= x y) `(,(%mkpat x) ,y))
  (x (if (pair? x) (map %mkpat x) x))))
(define-macro (|\|| . x) `(match-lambda* ,@(%mkpat x)))
(define-macro (-> x y) (match x
  (''() `(lambda () ,y))
  (x `(|\\a| (-> ,x ,y)))))
(define-macro (= x y) (match x
  (((or 'list '|::|) . _) `(match-define ,(%mkpat x) ,y))
  (_                      `(define ,x ,y))))
(define-macro (|:=| . x) (match (%mkpat x)
  ((f (_ ((_ 'opt) o) . xs)) `(define-syntax ,f (syntax-rules ,(%listm o) ,@xs)))
  ((f (_              . xs)) `(define-syntax ,f (syntax-rules  ()     ,@xs)))))
(define-macro (where x y) `(match-letrec ,(%mkpat (%where (%unsemc y))) ,x))
(define-macro (of x y) `((|\|| ,@(%unsemc y)) ,x))
(define (%cond x) (match x
  (((or 'then '?) x y) `(,x ,y))
  (               x    `(#t ,x))))
(define-macro (else . xs) `(cond ,@(map %cond xs)))
(define-macro (|:|  . xs) `(cond ,@(map %cond xs)))

(define (<p x) (memq x '(|(| |{| |[|)))
(define (>p x) (memq x '(|)| |}| |]|)))
(define (%op0 x) (and (%op x) (not (or (<p x) (>p x)))))
(define (%pre s) (regexp-replace-all* s #/^((#!|--)[^\n]*)*\n+/ "0\n"))
(define (%len m l) (match (#/\n+/ (m 2))
  (#f (+ (string-length (m)) l))
  (t     (string-length (t 'after)))))
(define ($->e s) (rxmatch-case s
  (#/(^[^$]*\$)\$(.*)/                  (#f s     ss) `(,s ,@($->e ss)))
  (#/(^[^$]*)\$([%&?]?)(\w+|{.+?})(.*)/ (#f s m x ss)
                      `(,s (enc ,m (x->string ,(parse x))) ,@($->e ss)))
  (else               `(,s))))
(define (%rd s) (rxmatch-case s
  (#/^<html/ () `(print header ,@($->e s)))
  (#/^'(.*)'$/ (#f x) (if (#/\$/ x) `(& ,@($->e x)) x))
  (#/^"/ () (let1 x (read-from-string (regexp-replace-all* s #/([^\\])"(.)/ "\\1\\")) (if (#/\$/ x) `(& ,@($->e x)) x)))
  (#/^`(.*)`$/ (#f x) (read-from-string x))
  (#/^[a-z]/ () (string->symbol (regexp-replace-all* s
    #/P$/ "?" #/Q$/ "!" #/S$/ "*" "2" "->"
    #/([a-z])([A-Z])/ (lambda (m) #`",(m 1)-,(char-downcase (ref (m 2) 0))")
    #/^to-/ "x->")))
  (#/^[\"#\w]/ () (read-from-string s))
  (else (string->symbol s))))
(define (%scan n s)
            ;(regexp             |#exp|html        |str1               |string         |symbl|num          |var|paren     |op
  (match (#/^(#\/(?:\\.|[^\/])*\/|#\S+|<html.*html>|'(?:\$.?{.*?}|.)*?'|"(?:\\.|[^"])*"|`.*?`|\d+(?:\.\d+)?|\w+|[()\[\]{}]|[^\w\s()\[\]{}#`"']+)(?:\s*-- [^\n]*)*(\s*)/ s)
    (#f ())
    (m (let* ((l (%len m n)) (x (%rd (m 1))) (xs (%scan l (m 'after)))) (cond 
      ((#/^(let|do|where|of|pp)$/ (m 1)) (match xs
        (('|{| . _)    `(,x ,@xs))
        (_             `(,x ("{}" ,l) ,@xs))))
      ((#/ *\n/ (m 2)) `(,x ("<>" ,l) ,@xs))
      (else            `(,x           ,@xs)))))))
(define (%L tss mss) (match `(,tss ,mss)
  ((ts ()) `(|(| ,@(%L ts '(0))))
  (((("<>" 0)) (0)) `(|)|))
  ;(((("{}" n) '|(| . ts) mss) `(|(| ,@(%L ts mss)))
  (((("{}" n)      . ts) mss) `(|(| ,@(%L ts `(,n ,@mss)))) ;note1
  ((((? >p p) . ts) (0 . ms)) `(,p  ,@(%L ts ms)))          ;note3
  ((((? >p p) . ts) (m . ms)) `(|)| ,@(%L tss ms)))         ;note3*
  ((((? <p p) . ts)      ms ) `(,p  ,@(%L ts `(0 ,@ms))))   ;note4
  (((and (("<>" n) . ts) tss) (and (m . ms) mss)) (cond
    ((> n m)              (%L ts mss))
    ((< n m)      `(|)| ,@(%L tss ms)))
    (else         `(|;| ,@(%L ts mss)))))
  (((t . ts) mss) `(,t  ,@(%L ts mss)))
  ((() mss) (%L '(("<>" 0)) mss))
  (x (error "%L" x))))
(define (%ap . xs) (match xs
  ((f x (g . y)) (if (and (eq? f g) (eq? (car (%op f)) 'a)) `(,f ,x ,@y) xs))
  (xs xs)))
(define (%reduce? . os) (match (map %op os)
  (((d1 n1) (d2 n2)) (if (eq? n1 n2) (eq? d1 'l) (> n1 n2)))
  (_ (error "%reduce?" os))))
(define (%sect f) (let1 g (gensym)
  (match-let1 (z . zs) (f g) `((lambda (,g) ,z) ,@zs))))
(define (%paren p x) (match `(,p ,x)
  (('|(| x) x)
  (('|[| ('|,| . xs)) `(list ,@xs))
  (('|{| ('|,| . xs)) `(dict ,@xs))
  (('|{| (and ('|:| . _) x)) `(dict ,x))
;  (('|{| ('|:| . xs)) `(dict (|:| ,@xs))
  (('|{| x) x)
;  (('|{| (and ((not '|:|) . _) x)) x)
  ((p x) (%paren p `(|,| ,x)))))
(define (%nil p) (match p ('|(| ''()) ('|[| ()) ('|{| '(hash-table 'equal?))))
(define (%parse x) (match x
  (((? <p p) (? >p) . xs) `(,(%nil p) ,@xs)) ;[]
  (((? <p  ) (? %op0 o) (? >p) . xs) `((id ,o) ,@xs))      ;(+)
  (((? <p p) (? %op0 o) . xs) (%sect (lambda (g) (%parse `(,p ,g ,o ,@xs))))) ;(+x)
  (((? <p p) . xs) (%pars `(,p -) (%pss xs)))
  (x x)))
(define (%pars x i) (match `(,x ,i)
  ((xs ((y) . is)) (%pars xs `(,y ,@is))) ;one arg
  ((xs (('infix lr n o) '|;| . is)) (set! (%op o) `(,lr ,n)) (%pars xs is))
  ((((? <p p) . _) (y (? >p) . is)) `(,(%paren p y) ,@is)) ;end
  ((xs (y (? %op0 o) (? >p p) . is)) (%sect (lambda (g) (%pars xs `(,y ,o ,g ,p ,@is)))));(x+)
  (((and (o1 x . xs) xss) (y (? %op o2) . is)) (cond
    ((%reduce? o1 o2) (%pars xs `(,(%ap o1 x y) ,o2 ,@is))) ;reduce
    (else            (%pars `(,o2 ,y ,@xss) (%pss is))))) ;shift
  (x (error "%pars" `(,x ,i)))))
(define (%pss x) (match (%parse x)
  (((? %op o) . xs) `(() ,o ,@xs))
  (((or 'if 'do 'case) . xs) (%pss xs))
  ;(((or ('id x) x) . xs) (match-let1 (y . ys) (%pss xs) `((,x ,@y) ,@ys)))
  (((or ('id x) x) . xs) (match (%pss xs)
    (((''()) . ys) `((apply ,x ()) ,@ys))
    ((y      . ys) `((,x ,@y)      ,@ys))))
  (x (error "%pss" x))))
(define (parse src) (%where (car (%parse (%L (%scan 0 (%pre src)) ())))))
(define (evl src) (eval (parse src) (interaction-environment)))

(define (hosh src) (let1 thunk (lambda () (evl
    (if (pair? *argv*) (call-with-input-file (car *argv*) port->string) src)))
  (if (sys-getenv "REQUEST_METHOD")
    (with-error-handler (lambda (e) (print header (ref e 'message))) thunk)
    (thunk))))
(evl "#!init
id x = x
f ... $ x := f ... x
f     $ x := f x
(f $$ x) := f $ x
x . f := f $ x
x -> y := (|) (x -> y)
let_ x in y := y where x
x & ... = stringAppend $@ toString <$> x
orig x := withModule gauche x
x + ... = orig (+) $@ toNumber <$> x
x - ... = orig (-) $@ toNumber <$> x
x * ... = orig (*) $@ toNumber <$> x
x / ... = orig (/) $@ toNumber <$> x
header = \"Content-Type: text/html; charset=UTF-8\\n\\n<!DOCTYPE html>\\n\"
open s 'w' f = callWithOutputFile s f
open s 'a' f = callWithOutputFile s f `:if-exists` `:append`
open s  _  f = callWithInputFile  s f
autoload `rfc.http` httpGet httpUserAgent
readFile f = case f =~ #/^http:..(.*?)(\\/.*)/ of
  #f -> callWithInputFile f port2string
  m  -> do httpUserAgent 'Mozilla/5.0 (iPhone; U; CPU like Mac OS X; en) AppleWebKit/420+ (KHTML, like Gecko) Version/3.0 Mobile/1C28 Safari/419.3'
           valuesRef (httpGet (m 1) (m 2)) 2
writeFile  f s = open f 'w' (display s $)
appendFile f s = open f 'a' (display s $)
split x y = stringSplit y x
join  x y = stringJoin  (map toString y) x
replace x y z = regexpReplaceAll x (z.toString) y
s =~ r = stringP s && rxmatch r s
x != y = !(x == y)
s !~ r = !(s =~ r)
x .. y = x>y ? []
       : x :: (x+1 .. y)
readHex n = hex n 0
  where hex 0 r = r
        hex n r = hex (n-1) (r*16 + digit2integer (readChar()) 16)
urlDecode s = withStringIo s (()-> portForEach wf readChar)
  where wf #\\% = writeByte $ readHex 2
        wf c    = writeChar (c == #\\+ ? #\\space : c)
hash x = hashTable $@ quote equalP :: x
cgidic = hash (qs =~ #/=/ ? kv <$> split #/&/ qs : [])
  where qs = sysGetenv 'REQUEST_METHOD' == 'POST'
           ? port2string $ standardInputPort()
           : sysGetenv 'QUERY_STRING'
        kv x = string2symbol k :: urlDecode v where [k,v] = split #/=/ x
cgi x := cgidic (quote x) || ''
readAll() = port2string $ currentInputPort()
argf f = af (cdr `*argv*`)
  where af []  = f()
        af [x] = withInputFromFile x f
        af xs  = map (x -> withInputFromFile x f) xs
awk f = argf (() -> portForEach (l -> f $ l :: l.split #/\\s/) readLine)
pf s (x::xs) = s & '(' & x & (apply (&) $ map (pf (s & '  ') $) xs) & ')'
pf s  x      =     ' ' & x
(pp x) := print $ pf '\n' $ quote x -- unwrapSyntax $ macroexpand $ quote x
show #t = 'True'
show #f = 'False'
show [] = '[]'
show (x::xs) = '[${show x}${shows xs}]'
show x = writeToString x
shows [] = ''
shows (x::xs) = ', ${show x}${shows xs}'
shows x = ' | ${show x}'
p x = print $ show x
dict (x:y) ... := hashTable (quote equalP) (toString (quote x) :: y) ...
autoload `rfc.mime` mimeEncodeText
enc '?' s = mimeEncodeText s `:charset` 'ISO-2022-JP'
enc '&' s = s.replace '&' '&amp;'.replace '<' '&lt;'.replace '>' '&gt;'
enc '%' s = withStringIo s (()-> portForEach wf readByte)
  where wf b = charSetContainsP #[\\w] (integer2char b) ? writeByte b
             : format #t \"%~2,'0x\" b
enc _ s = s
hread() = eofObjectP s ? s : parse s
  where s = readLine()
hprompt() = (display 'hosh> '; flush())
infix a 20 ~
x ~ ... = apply (&) x
autoload `gauche.charconv` cesConvert
toSjis s = cesConvert s 'UTF-8' 'CP932'
toJis  s = cesConvert s 'UTF-8' 'ISO-2022-JP'
toEuc  s = cesConvert s 'UTF-8' 'EUC-JP'
fromSjis s = cesConvert s 'CP932'     'UTF-8'
fromJis  s = cesConvert s 'ISO-2022-JP' 'UTF-8'
fromEuc  s = cesConvert s 'EUC-JP'    'UTF-8'
after m = m $ quote after
scan r f s = case s =~ r of
  #f -> []
  m  -> f m :: scan r f (m.after)
at n x = x n
autoload `gauche.process` callWithProcessIo callWithInputProcess
sh cmd     = callWithInputProcess cmd port2string
sh cmd dat = callWithProcessIo    cmd f
  where f ip op = do display dat op
                     closeOutputPort op
                     port2string ip
main arg = readEvalPrintLoop hread #f p hprompt
")
(hosh "")
