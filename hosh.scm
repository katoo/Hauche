#!/usr/local/bin/gosh
(define op (apply hash-table '(eq?
  (|.| l 19) (o a 19)
  (^ r 18) (* a 17) (/ a 17) (% l 17) (+ a 16) (- a 16)
  (~ a 15) (|::| r 15) (++ r 15) (.. r 15)
  (== l 14) (!= l 14) (< l 14) (<= l 14) (> l 14) (>= l 14) (=~ l 14) (!~ l 14)
  (&& a 13) (|\|\|| a 12)
  (<$> r 9) ($ r 9) ($@ r 9) (? r 8) (then r 8) (|:| a 7) (else a 7)
  (of l 6) (in r 6) (where r 6) (catch r 6)
  (-> a 5) (|\\| a 4) (<- r 3) (= r 3) (|:=| a 3) (|,| a 2) (|;| a 2) ($$ r 2)
  (|(| l 1) (|)| l 1) (|{| l 1) (|}| l 1) (|[| l 1) (|]| l 1))))
(define-syntax uses (syntax-rules () ((_ m ...)     (begin (use m) ...))))
(define-syntax defs (syntax-rules () ((_ (k v) ...) (begin (define k v) ...))))
(define-syntax macs (syntax-rules () ((_ (k v) ...) (begin (define-macro (k . x) `(v ,@x)) ...))))
(uses util.match)
(defs (|::| cons) (++ append) (== equal?) (^ expt) (% modulo) ($@ apply) (! not) (o compose) (<$> map))
(macs (<- set!) (then and) (? and) (&& and) (|\|\|| or) (|;| begin))
(define-method object-apply (obj key) (ref obj key #f))
(define-method (setter object-apply) (obj key val) (set! (ref obj key) val) obj)

(define (=? x) (memq x '(= |:=|)))
(define (np? x) (not (memq x '(|::| list))))
(define (whre xs) (match xs
  (() ())
;  ((('= (and ((or '|::| 'list) . _) a) b) . xs) `((= ,(mkpat a) ,b) ,@(whre xs)))
  ((((? =? o) ((? np? f) . a) b) . xs) (let
    ((c `(-> ,(if (eq? o '=) a `(_ ,@a)) ,b))
     (f? (pa$ eq? f))) (match (whre xs)
    ((((? =?) (? f?) ('|\\| . ps)) . xs) `((,o ,f (|\\| ,c ,@ps)) ,@xs))
    (                                xs  `((,o ,f (|\\| ,c     )) ,@xs)))))
  ((x . xs) `(,x ,@(whre xs)))
  (xs xs)))
(define (unsemc x) (match (whre x) (('|;| . x) x) (x `(,x))))
(define (onearg? x) (or (not (pair? x)) (memq (car x) '(|::| list))))
(define (listm x) (if (onearg? x) `(,x) x))
(define (mkpat x) (match x
  (('|::| x y) (cons (mkpat x) (mkpat y)))
  (('list . xs) (map mkpat xs))
  (('-> x y) `(,(listm (mkpat x)) ,y))
  (('= x y) `(,(mkpat x) ,y))
  (x (if (pair? x) (map mkpat x) x))))
(define-macro (|\\| . x) `(match-lambda* ,@(mkpat x)))
(define-macro (= x y) `(match-define ,(mkpat x) ,y))
(define-macro (|:=| . x) (match (mkpat x)
  ((f (_ ((_ 'opt) o) . xs)) `(define-syntax ,f (syntax-rules ,(listm o) ,@xs)))
  ((f (_              . xs)) `(define-syntax ,f (syntax-rules  ()     ,@xs)))))
(define-macro (where x y) `(match-letrec ,(mkpat (unsemc y)) ,x))
(define-macro (of x y) (match y
  (('|;| . ys) `((|\\| ,@ys) ,x))
  (        y   `((|\\|  ,y ) ,x))))
(define (cnd x) (match x
  (((or 'then '?) x y) `(,x ,y))
  (               x    `(#t ,x))))
(define-macro (else . xs) `(cond ,@(map cnd xs)))
(define-macro (|:|  . xs) `(cond ,@(map cnd xs)))
(define-macro (call x) `(,x))

;(define (evl src)
(define (<? x) (memq x '(|(| |{| |[|)))
(define (>? x) (memq x '(|)| |}| |]|)))
(define (op0 x) (and (op x) (not (or (<? x) (>? x)))))
(define (pre s) (regexp-replace-all* s
  #/#![^\n]*\n*/ ""
  #/<html.*html>/ "print header ``\\0``"
  #/<%=(.*?)%>/ "`` (\\1) ``"))
(define (len m l)
  (match (#/\n+/ (m 2))
    (#f (+ (string-length (m)) l))
    (t     (string-length (t 'after)))))
(define ($->e s) (rxmatch-case s
  (#/([^$]*\$)\$(.*)/    (#f s   ss) `(,s ,@($->e ss)))
  (#/([^$]*)\${(.+?)}(.*)/ (#f s x ss) `(,s ,(p&s x) ,@($->e ss)))
  (#/([^$]*)\$(\w+)(.*)/ (#f s x ss) `(,s ,(string->symbol x) ,@($->e ss)))
  (else `(,s))))
(define (rd s) (rxmatch-case s
  (#/^``(.*)``$/ (#f x) `(~ ,@($->e x)))
  (#/^'(.*)'$/ (#f x) (read-from-string x))
  (#/^[a-z]/ () (string->symbol (regexp-replace-all* s
    #/P$/ "?" #/Q$/ "!" #/S$/ "*" "2" "->"
    #/([a-z])([A-Z])/ (lambda (m) #`",(m 1)-,(char-downcase (ref (m 2) 0))")
    #/^to-/ "x->")))
  (#/^[\"#\w]/ () (read-from-string s))
  (else (string->symbol s))))
(define (scan s n)
            ;(regexp             |#exp|heardoc|string         |symbl|num          |var|paren     |op
  (match (#/^(#\/(?:\\.|[^\/])*\/|#\S+|``.*?``|"(?:\\.|[^"])*"|'.*?'|\d+(?:\.\d+)?|\w+|[()\[\]{}]|[^\w\s()\[\]{}#`"']+)(?:\s*-- [^\n]*)*(\s*)/ s)
    (#f ())
    (m (let* ((l (len m n)) (x (rd (m 1))) (xs (scan (m 'after) l))) (cond 
      ((#/^(let|do|where|of)$/ (m 1)) `(,x ("{}" ,l) ,@xs))
      ((#/ *\n/ (m 2))                `(,x ("<>" ,l) ,@xs))
      (else                           `(,x           ,@xs)))))))
(define L (match-lambda*
  ((ts) (L `(|(| ,@ts) '(0)))
  (((or () (("<>" 0))) (0)) `(|)|))
  (((("{}" n) '|(| . ts) mss) `(|(| ,@(L ts mss)))
  (((("{}" n)      . ts) mss) `(|(| ,@(L ts `(,n ,@mss))))
  (((and (("<>" n) . ts) tss) (and (m . ms) mss)) (cond
    ((> n m)              (L ts mss))
    ((< n m)      `(|)| ,@(L tss ms)))
    (else         `(|;| ,@(L ts mss)))))
  (((t . ts) mss) `(,t  ,@(L ts mss)))
  (x (error "L" x))))
(define (ap . xs) (match xs
  ((f x (g . y)) (if (and (eq? f g) (eq? (car (op f)) 'a)) `(,f ,x ,@y) xs))
  (xs xs)))
(define (reduce? . os) (match (map op os)
  (((d1 n1) (d2 n2)) (if (eq? n1 n2) (eq? d1 'l) (> n1 n2)))
  (_ (error "reduce?" os))))
(define (sect f) (let1 g (gensym)
  (match-let1 (z . zs) (f g) `((lambda (,g) ,z) ,@zs))))
(define (paren p x) (match `(,p ,x)
  (('|(| x) x)
  (('|[| ('|,| . xs)) `(list ,@xs))
  (('|{| ('|,| . xs)) `(dict ,@xs))
  ((p x) (paren p `(|,| ,x)))))
(define (parse x) (match x
  (((? <? p) (? >?) . xs) `(() ,@xs)) ;`(,(paren p '(|,|)) ,@xs)      ;[]
  (((? <?  ) (? op0 o) (? >?) . xs) `((id ,o) ,@xs))      ;(+)
  (((? <? p) '-> . xs) (match-let1 (y . ys) (parse `(,p ,@xs)) `((lambda () ,y) ,@ys))) ;(->x) 
  (((? <? p) (? op0 o) . xs) (sect (lambda (g) (parse `(,p ,g ,o ,@xs))))) ;(+x)
  (((? <? p) . xs) (pars `(,p -) (pss xs)))
  (x x)))
(define (pars x i) (match `(,x ,i)
  ((xs ((y) . is)) (pars xs `(,y ,@is))) ;one arg
  ((xs (('infix lr n o) '|;| . is)) (set! (op o) `(,lr ,n)) (pars xs is))
  ((((? <? p) . _) (y (? >?) . is)) `(,(paren p y) ,@is)) ;end
  ((xs (y (? op0 o) (? >? p) . is)) (sect (lambda (g) (pars xs `(,y ,o ,g ,p ,@is)))));(x+)
  (((and (o1 x . xs) xss) (y (? op o2) . is)) (cond
    ((reduce? o1 o2) (pars xs `(,(ap o1 x y) ,o2 ,@is))) ;reduce
    (else            (pars `(,o2 ,y ,@xss) (pss is))))) ;shift
  (x (error "pars" x))))
(define (pss x) (match (parse x)
  (((? op o) . xs) `(() ,o ,@xs))
  (((or 'if 'do 'case) . xs) (pss xs))
  (((or ('id x) x) . xs) (match-let1 (y . ys) (pss xs) `((,x ,@y) ,@ys)))
  (x (error "pss" x))))
(define (p&s src) (whre (car (parse (L (scan (pre src) 0))))))
(define (evl src) (eval (p&s src) (interaction-environment)))

(define (hosh src) (let1 thunk (lambda () (evl
    (if (pair? *argv*) (call-with-input-file (car *argv*) port->string) src)))
  (if (sys-getenv "REQUEST_METHOD")
    (with-error-handler (lambda (e) (print header (ref e 'message))) thunk)
    (thunk))))
(evl "#!init
f ... $ x := f ... x
f     $ x := f x
(f $$ x) := f $ x
x . f := f $ x
x -> y := (\\) (x -> y)
let_ x in y := y where x
x ~ ... = stringAppend $@ toString <$> x
x + ... = withModule gauche (+) $@ x2number <$> x
header = \"Content-Type: text/html; charset=UTF-8\\n\\n<!DOCTYPE html>\\n\"
open s \"w\" f = callWithOutputFile s f
open s \"a\" f = callWithOutputFile s f ':if-exists' ':append'
open s _     f = callWithInputFile  s f
readFile   f   = open f \"r\" port2string
writeFile  f s = open f \"w\" (display s $)
appendFile f s = open f \"a\" (display s $)
split x y = stringSplit y x
join  x y = stringJoin  (map toString y) x
replace x y z = regexpReplaceAll x z y
s =~ r = stringP s && rxmatch r s
x != y = !(x == y)
s !~ r = !(s =~ r)
x .. y = x>y ? []
       : x :: (x+1 .. y)
readHex n = hex n 0
  where hex 0 r = r
        hex n r = hex (n-1) (r*16 + digit2integer (call readChar) 16)
urlDecode s = withStringIo s (-> portForEach wf readChar)
  where wf #\\% = writeByte $ readHex 2
        wf c    = writeChar (c == #\\+ ? #\\space : c)
hash x = hashTable $@ quote equalP :: x
cgidic = hash (qs =~ #/=/ ? kv <$> split #/&/ qs : [])
  where qs = sysGetenv \"REQUEST_METHOD\" == \"POST\"
           ? port2string $ call standardInputPort
           : sysGetenv \"QUERY_STRING\"
        kv x = string2symbol k :: urlDecode v where [k,v] = split #/=/ x
cgi x := cgidic (quote x) || \"\"
htmlEsc x = x.toString.replace #/</ \"&lt;\"
argf [] f = portForEach f readLine
argf xs f = forEach (x -> withInputFromFile x (->portForEach f readLine)) xs
pf s (x::xs) = s ~ \"(\" ~ x ~ (apply (~) $ map (pf (s ~ \"  \") $) xs) ~ \")\"
pf s  x      =     \" \" ~ x
pp x := print $ pf \"\n\" $ unwrapSyntax $ macroexpand $ quote x
show #t = \"True\"
show #f = \"False\"
show [] = \"[]\"
show (x::xs) = \"[\" ~ join \", \" (map show (x::xs)) ~ \"]\"
show x = x.toString
p x = print $ show x
dict (x:y) ... := hashTable (quote equalP) (toString (quote x) :: y) ...
")
(hosh "a=1
print ``xx${a}x${a+a}x$a``
")
