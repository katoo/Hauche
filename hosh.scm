#!/usr/local/bin/gosh
(define-syntax uses (syntax-rules () ((_ m ...) (begin (use m) ...))))
(define-syntax defs (syntax-rules () ((_ (k v) ...) (begin (define k v) ...))))
(define-syntax macs (syntax-rules () ((_ (k v) ...) (begin (define-macro (k . x) `(v ,@x)) ...))))
(uses util.match)
(defs (|[]| list) (|:| cons) (++ append) (== equal?))
(macs (= define) (<- set!) (fn match-lambda*) (do begin) (|;| begin))
(define-method object-apply (obj key) (ref obj key #f))
(define-method (setter object-apply) (obj key val) (set! (ref obj key) val) obj)
(define (replace x y z) (regexp-replace-all* z x y))
(define (len m l)
  (match (#/\n+/ (m 2))
    (#f (+ (string-length (m)) l))
    (t     (string-length (t 'after)))))
(define (rd s) (rxmatch-case s
  (#/^''(.*)''$/ (#f x) x)
  (#/^[\"#\w]/ () (read-from-string s))
  (else (string->symbol s))))
(define (scan s n)
            ;(regexp             |heardoc|string         |var|paren     |op
  (match (#/^(#\/(?:\\.|[^\/])*\/|``.*?``|"(?:\\.|[^"])*"|\w+|[()\[\]{}]|[^\w\s()\[\]{}"']+)(?: *-- [^\n]*)?(\s*)/ s)
    (#f ())
    (m (let* ((l (len m n)) (x (rd (m 1))) (xs (scan (m 'after) l))) (cond 
      ((#/^(let|do|where|\\|\||of)$/ (m 1)) `(,x ("{}" ,l) ,@xs))
      ((#/ *\n/ (m 2))                `(,x ("<>" ,l) ,@xs))
      (else                           `(,x           ,@xs)))))))
(define L (match-lambda*
  ((ts) (L `(|(| ,@ts) '(0)))
  (((("<>" 0)) (0)) `(|)|))
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
(define op (apply hash-table '(eq?
  (^ r 19) (* a 18) (/ a 18) (+ a 17) (- a 17)
  (& a 16) (|:| r 16) (++ r 16) (.. r 16)
  (== l 15) (!= l 15) (< l 15) (<= l 15) (> l 15) (>= l 15) (and a 14) (or a 14)
  ($ r 9) (|.| l 9) (? r 8) (then r 8) (! a 7) (else a 7)
  (match l 4) (in r 4) (where r 4) (catch r 4) (--> r 3)
  (-> a 3) (|\|| a 2) (<- r 1) (= r 1) (|:=| a 1) (|,| a 0) (|;| a 0)
  (|(| l -1) (|)| l -1) (|{| l -1) (|}| l -1) (|[| l -1) (|]| l -1) (-- l -2))))
(define (<? x) (memq x '(|(| |{| |[|)))
(define (>? x) (memq x '(|)| |}| |]|)))
(define (op0 x) (and (op x) (not (or (<? x) (>? x)))))
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
  (((? <? p) (? op0 o) . xs) (sect (^g (parse `(,p ,g ,o ,@xs))))) ;(+x)
  (((? <? p) . xs) (pars `(,p -) (pss xs)))
  (x x)))
(define (pars x i) (match `(,x ,i)
  ((xs ((y) . is)) (pars xs `(,y ,@is))) ;one arg
  ((xs (('infix lr n o) '|;| . is)) (set! (op o) `(,lr ,n)) (pars xs is))
  ((((? <? p) . _) (y (? >?) . is)) `(,(paren p y) ,@is)) ;end
  ((xs (y (? op0 o) (? >? p) . is)) (sect (^g (pars xs `(,y ,o ,g ,p ,@is)))));(x+)
  (((and (o1 x . xs) xss) (y (? op o2) . is)) (cond
    ((reduce? o1 o2) (pars xs `(,(ap o1 x y) ,o2 ,@is))) ;reduce
    (else            (pars `(,o2 ,y ,@xss) (pss is))))) ;shift
  (x (error "pars" x))))
(define (pss x) (match (parse x)
  (((? op o) . xs) `(() ,o ,@xs))
  ((x . xs) (match-let1 (y . ys) (pss xs) `((,x ,@y) ,@ys)))))
(define (whre xs) (match xs
  (() ())
  ((('= (f . a) b) . xs) (let1 f? (pa$ eq? f) (match (whre xs)
    ((('= (? f?) ('|\\| . ps)) . xs) `((= ,f (|\\| (-> ,a ,b) ,@ps)) ,@xs))
    (xs                              `((= ,f (|\\| (-> ,a ,b)     )) ,@xs)))))
  ((x . xs) `(,x ,@(whre xs)))))
(define (onearg? x) (or (not (pair? x)) (memq (car x) '(|:| list))))
(define (mkpat x) (match x
  (('|:| x y) (cons (mkpat x) (mkpat y)))
  (('list . xs) (map mkpat xs))
  (('-> x y) (if (onearg? x) `((,(mkpat x)) ,y) `(,(mkpat x) ,y)))
  (x (if (pair? x) (map mkpat x) x))))
(define-macro ( $  x y) (if (pair? x) `(,@x ,y) `(,x ,y)))
(define-macro (|\\| . x) `(match-lambda* ,@(mkpat x)))
(define src "#!/usr/bin/env hosh
[] ++ y = y
(x:xs) ++ y = x : (xs ++ y)
print $ [1,2] ++ [3,4]
fact 0 = 1
fact n = n * fact (n-1)
print $ fact 4
")
(define (evl s) (eval (whre (car (parse (L (scan s 0))))) (interaction-environment)))
(define (p s xs) (match xs
  ((x . xs) (format #t "\n~A(~A" s x) (map (pa$ p #`"  ,s") xs) (format #t ")"))
  (_ (format #t " ~A" xs))))
;(p "" (mkpat (whre (car (parse (L (scan (replace #/^#!.*?\n/ "" src) 0)))))))
(let1 thunk (lambda () (evl (replace #/^#!.*?\n/ ""
  (if (pair? *argv*)
    (call-with-input-file (car *argv*) port->string)
    src))))
  (if (sys-getenv "REQUEST_METHOD")
    (with-error-handler (lambda (e) (print "Content-type: text/plain\n\n" (ref e 'message))) thunk)
    (thunk)))
