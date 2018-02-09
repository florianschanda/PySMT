(set-logic AUFBVLIRA)
(set-info :source |VC generated by SPARK 2014|)
(set-info :smt-lib-version 2.0)
(set-info :category industrial)
(set-info :status unknown) ; strongly presumed unsat

(declare-sort uni 0)

(declare-sort ty 0)

(declare-fun sort (ty uni) Bool)

(declare-fun witness (ty) uni)

;; witness_sort
  (assert (forall ((a ty)) (sort a (witness a))))

(declare-fun int () ty)

(declare-fun real () ty)

(declare-fun bool () ty)

(declare-fun match_bool (ty Bool uni uni) uni)

;; match_bool_sort
  (assert
  (forall ((a ty))
  (forall ((x Bool) (x1 uni) (x2 uni)) (sort a (match_bool a x x1 x2)))))

;; match_bool_True
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni)) (=> (sort a z) (= (match_bool a true z z1) z)))))

;; match_bool_False
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (=> (sort a z1) (= (match_bool a false z z1) z1)))))

(declare-fun index_bool (Bool) Int)

;; index_bool_True
  (assert (= (index_bool true) 0))

;; index_bool_False
  (assert (= (index_bool false) 1))

(declare-fun tuple0 () ty)

(declare-fun Tuple0 () uni)

;; Tuple0_sort
  (assert (sort tuple0 Tuple0))

(declare-fun qtmark () ty)

(declare-fun ref (ty) ty)

(declare-fun mk_ref (ty uni) uni)

;; mk ref_sort
  (assert (forall ((a ty)) (forall ((x uni)) (sort (ref a) (mk_ref a x)))))

(declare-fun contents (ty uni) uni)

;; contents_sort
  (assert (forall ((a ty)) (forall ((x uni)) (sort a (contents a x)))))

;; contents_def
  (assert
  (forall ((a ty))
  (forall ((u uni)) (=> (sort a u) (= (contents a (mk_ref a u)) u)))))

(declare-fun us__ignore (ty uni) uni)

;; ___ignore_sort
  (assert
  (forall ((a ty)) (forall ((x uni)) (sort tuple0 (us__ignore a x)))))

(declare-fun us_private () ty)

(declare-fun us_null_ext__ () uni)

;; __null_ext___sort
  (assert (sort us_private us_null_ext__))

(declare-fun us_type_of_heap () ty)

(declare-fun us_image () ty)

(declare-sort t 0)

(declare-fun t1 () ty)

(declare-sort us_t 0)

(declare-fun us_t1 () ty)

(declare-sort t2 0)

(declare-fun t3 () ty)

(declare-sort us_t2 0)

(declare-fun us_t3 () ty)

(declare-sort t4 0)

(declare-fun t5 () ty)

(declare-sort byte_t 0)

(declare-fun byte_t1 () ty)

(declare-sort integer 0)

(declare-fun integer1 () ty)

(declare-fun t6 () ty)

(declare-fun map1 (ty ty) ty)

(declare-fun ite1 (ty Bool uni uni) uni)

;; ite_sort
  (assert
  (forall ((a ty))
  (forall ((x Bool) (x1 uni) (x2 uni)) (sort a (ite1 a x x1 x2)))))

(define-fun to_int1 ((b Bool)) Int (ite (= b true) 1 0))

(define-fun of_int ((i Int)) Bool (ite (= i 0) false true))

(define-fun in_range ((x Int)) Bool (or (= x 0) (= x 1)))

(declare-fun attr__ATTRIBUTE_IMAGE (Bool) uni)

;; attr__ATTRIBUTE_IMAGE_sort
  (assert (forall ((x Bool)) (sort us_image (attr__ATTRIBUTE_IMAGE x))))

(declare-fun attr__ATTRIBUTE_VALUE__pre_check (uni) Bool)

(declare-fun attr__ATTRIBUTE_VALUE (uni) Bool)

(declare-fun pow2 (Int) Int)

(define-fun uint_in_range ((i Int)) Bool (and (<= 0 i) (<= i 255)))

(declare-fun nth ((_ BitVec 8) Int) Bool)

(declare-fun lsr ((_ BitVec 8) Int) (_ BitVec 8))

;; lsr_bv_is_lsr
  (assert
  (forall ((x (_ BitVec 8)) (n (_ BitVec 8)))
  (= (bvlshr x n) (lsr x (bv2nat n)))))

(declare-fun asr ((_ BitVec 8) Int) (_ BitVec 8))

;; asr_bv_is_asr
  (assert
  (forall ((x (_ BitVec 8)) (n (_ BitVec 8)))
  (= (bvashr x n) (asr x (bv2nat n)))))

(declare-fun lsl ((_ BitVec 8) Int) (_ BitVec 8))

;; lsl_bv_is_lsl
  (assert
  (forall ((x (_ BitVec 8)) (n (_ BitVec 8)))
  (= (bvshl x n) (lsl x (bv2nat n)))))

;; two_power_size_val
  (assert (= (+ 255 1) (pow2 8)))

(declare-fun power ((_ BitVec 8) Int) (_ BitVec 8))

(define-fun in_range1 ((x Int)) Bool (and (<= (- 2147483648) x)
                                     (<= x 2147483647)))

(define-fun bool_eq ((x Int) (y Int)) Bool (ite (= x y) true false))

(declare-fun attr__ATTRIBUTE_IMAGE1 (Int) uni)

;; attr__ATTRIBUTE_IMAGE_sort
  (assert (forall ((x Int)) (sort us_image (attr__ATTRIBUTE_IMAGE1 x))))

(declare-fun attr__ATTRIBUTE_VALUE__pre_check1 (uni) Bool)

(declare-fun attr__ATTRIBUTE_VALUE1 (uni) Int)

(declare-fun to_rep (integer) Int)

(declare-fun of_rep (Int) integer)

(declare-fun user_eq (integer integer) Bool)

(declare-fun dummy () integer)

;; inversion_axiom
  (assert
  (forall ((x integer)) (! (= (of_rep (to_rep x)) x) :pattern ((to_rep x)) )))

;; range_axiom
  (assert
  (forall ((x integer)) (! (in_range1 (to_rep x)) :pattern ((to_rep x)) )))

;; coerce_axiom
  (assert
  (forall ((x Int))
  (! (=> (in_range1 x) (= (to_rep (of_rep x)) x)) :pattern ((to_rep
                                                            (of_rep x))) )))

(declare-fun get (ty ty uni uni) uni)

;; get_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni)) (sort b (get b a x x1)))))

(declare-fun set (ty ty uni uni uni) uni)

;; set_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni) (x1 uni) (x2 uni)) (sort (map1 a b) (set b a x x1 x2)))))

(declare-fun const1 (ty ty uni) uni)

;; const_sort
  (assert
  (forall ((a ty) (b ty))
  (forall ((x uni)) (sort (map1 a b) (const1 b a x)))))

(declare-fun const2 (byte_t) (Array Int byte_t))

;; Const
  (assert (forall ((b byte_t) (a Int)) (= (select (const2 b) a) b)))

;; Const
  (assert
  (forall ((a ty) (b ty))
  (forall ((b1 uni) (a1 uni))
  (=> (sort b b1) (= (get b a (const1 b a b1) a1) b1)))))

(declare-fun bool_eq1 (ty uni Int Int uni Int Int) Bool)

(declare-fun bool_eq2 ((Array Int byte_t) Int Int (Array Int byte_t) Int
  Int) Bool)

;; T__ada_array___equal_def
  (assert
  (forall ((a (Array Int byte_t)))
  (forall ((af Int))
  (forall ((al Int))
  (forall ((b (Array Int byte_t)))
  (forall ((bf Int))
  (forall ((bl Int))
  (! (=
     (and (ite (<= af al) (= (+ (- al af) 1) (+ (- bl bf) 1)) (< bl bf))
     (forall ((i Int))
     (! (=> (and (<= af i) (<= i al))
        (= (select a i) (select b (+ (- bf af) i)))) :pattern ((select a i)) )))
     (= (bool_eq2 a af al b bf bl) true)) :pattern ((bool_eq2 a af al b bf
                                                    bl)) ))))))))

(declare-fun t2tb (Int) uni)

;; t2tb_sort
  (assert (forall ((x Int)) (sort int (t2tb x))))

(declare-fun tb2t (uni) Int)

;; BridgeL
  (assert (forall ((i Int)) (! (= (tb2t (t2tb i)) i) :pattern ((t2tb i)) )))

;; BridgeR
  (assert
  (forall ((j uni)) (! (= (t2tb (tb2t j)) j) :pattern ((t2tb (tb2t j))) )))

;; T__ada_array___equal_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni))
  (forall ((af Int))
  (forall ((al Int))
  (forall ((b uni))
  (forall ((bf Int))
  (forall ((bl Int))
  (! (=
     (and (ite (<= af al) (= (+ (- al af) 1) (+ (- bl bf) 1)) (< bl bf))
     (forall ((i Int))
     (! (=> (and (<= af i) (<= i al))
        (= (get a int a1 (t2tb i)) (get a int b (t2tb (+ (- bf af) i))))) :pattern (
     (get a int a1 (t2tb i))) ))) (= (bool_eq1 a a1 af al b bf bl) true)) :pattern (
  (bool_eq1 a a1 af al b bf bl)) )))))))))

(declare-fun slide (ty uni Int Int) uni)

;; slide_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 Int) (x2 Int)) (sort (map1 int a) (slide a x x1 x2)))))

(declare-fun slide1 ((Array Int byte_t) Int Int) (Array Int byte_t))

;; slide_eq
  (assert
  (forall ((a (Array Int byte_t)))
  (forall ((first Int))
  (! (= (slide1 a first first) a) :pattern ((slide1 a first first)) ))))

;; slide_eq
  (assert
  (forall ((a ty))
  (forall ((a1 uni))
  (=> (sort (map1 int a) a1)
  (forall ((first Int))
  (! (= (slide a a1 first first) a1) :pattern ((slide a a1 first first)) ))))))

;; slide_def
  (assert
  (forall ((a (Array Int byte_t)))
  (forall ((old_first Int))
  (forall ((new_first Int))
  (forall ((i Int))
  (! (= (select (slide1 a old_first new_first) i) (select a (- i (- new_first old_first)))) :pattern ((select
  (slide1 a old_first new_first) i)) ))))))

;; slide_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni))
  (forall ((old_first Int))
  (forall ((new_first Int))
  (forall ((i Int))
  (! (= (get a int (slide a a1 old_first new_first) (t2tb i)) (get a
                                                              int a1
                                                              (t2tb
                                                              (- i (- new_first old_first))))) :pattern (
  (get a int (slide a a1 old_first new_first) (t2tb i))) )))))))

(declare-fun concat1 (ty uni Int Int uni Int Int) uni)

;; concat_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 Int) (x2 Int) (x3 uni) (x4 Int) (x5 Int)) (sort
  (map1 int a) (concat1 a x x1 x2 x3 x4 x5)))))

(declare-fun concat2 ((Array Int byte_t) Int Int (Array Int byte_t) Int
  Int) (Array Int byte_t))

;; concat_def
  (assert
  (forall ((a (Array Int byte_t)) (b (Array Int byte_t)))
  (forall ((a_first Int) (a_last Int) (b_first Int) (b_last Int))
  (forall ((i Int))
  (! (and
     (=> (and (<= a_first i) (<= i a_last))
     (= (select (concat2 a a_first a_last b b_first b_last) i) (select a i)))
     (=> (< a_last i)
     (= (select (concat2 a a_first a_last b b_first b_last) i) (select b (+ (- i a_last) (- b_first 1)))))) :pattern ((select
  (concat2 a a_first a_last b b_first b_last) i)) )))))

;; concat_def
  (assert
  (forall ((a ty))
  (forall ((a1 uni) (b uni))
  (forall ((a_first Int) (a_last Int) (b_first Int) (b_last Int))
  (forall ((i Int))
  (! (and
     (=> (and (<= a_first i) (<= i a_last))
     (= (get a int (concat1 a a1 a_first a_last b b_first b_last) (t2tb i))
     (get a int a1 (t2tb i))))
     (=> (< a_last i)
     (= (get a int (concat1 a a1 a_first a_last b b_first b_last) (t2tb i))
     (get a int b (t2tb (+ (- i a_last) (- b_first 1))))))) :pattern (
  (get a int (concat1 a a1 a_first a_last b b_first b_last) (t2tb i))) ))))))

(declare-fun compare (ty uni Int Int uni Int Int) Int)

(declare-fun compare1 ((Array Int byte_t) Int Int (Array Int byte_t) Int
  Int) Int)

(declare-fun xorb (ty uni Int Int uni Int Int) uni)

;; xorb_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 Int) (x2 Int) (x3 uni) (x4 Int) (x5 Int)) (sort
  (map1 int a) (xorb a x x1 x2 x3 x4 x5)))))

(declare-fun xorb1 ((Array Int byte_t) Int Int (Array Int byte_t) Int
  Int) (Array Int byte_t))

(declare-fun andb (ty uni Int Int uni Int Int) uni)

;; andb_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 Int) (x2 Int) (x3 uni) (x4 Int) (x5 Int)) (sort
  (map1 int a) (andb a x x1 x2 x3 x4 x5)))))

(declare-fun andb1 ((Array Int byte_t) Int Int (Array Int byte_t) Int
  Int) (Array Int byte_t))

(declare-fun orb (ty uni Int Int uni Int Int) uni)

;; orb_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 Int) (x2 Int) (x3 uni) (x4 Int) (x5 Int)) (sort
  (map1 int a) (orb a x x1 x2 x3 x4 x5)))))

(declare-fun orb1 ((Array Int byte_t) Int Int (Array Int byte_t) Int
  Int) (Array Int byte_t))

(declare-fun notb (ty uni Int Int) uni)

;; notb_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 Int) (x2 Int)) (sort (map1 int a) (notb a x x1 x2)))))

(declare-fun notb1 ((Array Int byte_t) Int Int) (Array Int byte_t))

(declare-fun singleton (ty uni Int) uni)

;; singleton_sort
  (assert
  (forall ((a ty))
  (forall ((x uni) (x1 Int)) (sort (map1 int a) (singleton a x x1)))))

(declare-fun singleton1 (byte_t Int) (Array Int byte_t))

;; singleton_def
  (assert
  (forall ((v byte_t))
  (forall ((i Int))
  (! (= (select (singleton1 v i) i) v) :pattern ((select (singleton1 v i) i)) ))))

;; singleton_def
  (assert
  (forall ((a ty))
  (forall ((v uni))
  (=> (sort a v)
  (forall ((i Int))
  (! (= (get a int (singleton a v i) (t2tb i)) v) :pattern ((get a int
                                                            (singleton a v i)
                                                            (t2tb i))) ))))))

(define-fun in_range2 ((x (_ BitVec 8))) Bool (and (bvule ((_ int2bv 8) 0) x)
                                              (bvule x ((_ int2bv 8) 255))))

(define-fun in_range_int ((x Int)) Bool (and (<= 0 x) (<= x 255)))

(define-fun bool_eq3 ((x (_ BitVec 8))
  (y (_ BitVec 8))) Bool (ite (= x y) true false))

(declare-fun attr__ATTRIBUTE_IMAGE2 ((_ BitVec 8)) uni)

;; attr__ATTRIBUTE_IMAGE_sort
  (assert
  (forall ((x (_ BitVec 8))) (sort us_image (attr__ATTRIBUTE_IMAGE2 x))))

(declare-fun attr__ATTRIBUTE_VALUE__pre_check2 (uni) Bool)

(declare-fun attr__ATTRIBUTE_VALUE2 (uni) (_ BitVec 8))

(declare-fun to_rep1 (byte_t) (_ BitVec 8))

(declare-fun of_rep1 ((_ BitVec 8)) byte_t)

(declare-fun user_eq1 (byte_t byte_t) Bool)

(declare-fun dummy1 () byte_t)

;; inversion_axiom
  (assert
  (forall ((x byte_t))
  (! (= (of_rep1 (to_rep1 x)) x) :pattern ((to_rep1 x)) )))

;; range_axiom
  (assert
  (forall ((x byte_t)) (! (in_range2 (to_rep1 x)) :pattern ((to_rep1 x)) )))

(define-fun to_int2 ((x byte_t)) Int (bv2nat (to_rep1 x)))

;; range_int_axiom
  (assert
  (forall ((x byte_t)) (! (in_range_int
  (to_int2 x)) :pattern ((to_int2 x)) )))

;; coerce_axiom
  (assert
  (forall ((x (_ BitVec 8)))
  (! (= (to_rep1 (of_rep1 x)) x) :pattern ((to_rep1 (of_rep1 x))) )))

(declare-fun first (t4) integer)

(declare-fun last (t4) integer)

(declare-fun mk (Int Int) t4)

;; mk_def
  (assert
  (forall ((f Int) (l Int))
  (! (=> (in_range1 f)
     (=> (in_range1 l)
     (and (= (to_rep (first (mk f l))) f) (= (to_rep (last (mk f l))) l)))) :pattern (
  (mk f l)) )))

(define-fun dynamic_property ((range_first Int) (range_last Int) (low Int)
  (high Int)) Bool (and (in_range1 low)
                   (and (in_range1 high)
                   (=> (<= low high) (and (in_range1 low) (in_range1 high))))))

(declare-fun mk___t ((Array Int byte_t) t4) us_t2)

(declare-fun elts (us_t2) (Array Int byte_t))

;; elts_def
  (assert
  (forall ((u (Array Int byte_t)) (u1 t4)) (= (elts (mk___t u u1)) u)))

(declare-fun rt (us_t2) t4)

;; rt_def
  (assert
  (forall ((u (Array Int byte_t)) (u1 t4)) (= (rt (mk___t u u1)) u1)))

(define-fun of_array ((a (Array Int byte_t)) (f Int)
  (l Int)) us_t2 (mk___t a (mk f l)))

(define-fun first1 ((a us_t2)) Int (to_rep (first (rt a))))

(define-fun last1 ((a us_t2)) Int (to_rep (last (rt a))))

(define-fun length ((a us_t2)) Int (ite (<= (first1 a) (last1 a))
                                   (+ (- (last1 a) (first1 a)) 1) 0))

(declare-fun value__size () Int)

(declare-fun object__size ((Array Int byte_t)) Int)

;; value__size_axiom
  (assert (<= 0 value__size))

;; object__size_axiom
  (assert (forall ((a (Array Int byte_t))) (<= 0 (object__size a))))

(define-fun bool_eq4 ((x us_t2)
  (y us_t2)) Bool (bool_eq2 (elts x) (to_rep (first (rt x)))
                  (to_rep (last (rt x))) (elts y) (to_rep (first (rt y)))
                  (to_rep (last (rt y)))))

(declare-fun user_eq2 (us_t2 us_t2) Bool)

(declare-fun dummy2 () us_t2)

;; compare_def
  (assert
  (forall ((a (Array Int byte_t)) (b (Array Int byte_t)))
  (forall ((a_first Int) (a_last Int) (b_first Int) (b_last Int))
  (! (and
     (= (= (compare1 a a_first a_last b b_first b_last) 0)
     (= (bool_eq2 a a_first a_last b b_first b_last) true))
     (and
     (= (< (compare1 a a_first a_last b b_first b_last) 0)
     (exists ((i Int) (j Int))
     (and (<= i a_last)
     (and (< j b_last)
     (and (= (bool_eq2 a a_first i b b_first j) true)
     (or (= i a_last)
     (and (< i a_last)
     (bvult (to_rep1 (select a (+ i 1))) (to_rep1 (select b (+ j 1)))))))))))
     (= (< 0 (compare1 a a_first a_last b b_first b_last))
     (exists ((i Int) (j Int))
     (and (<= i b_last)
     (and (< j a_last)
     (and (= (bool_eq2 a a_first j b b_first i) true)
     (or (= i b_last)
     (and (< i b_last)
     (bvugt (to_rep1 (select a (+ j 1))) (to_rep1 (select b (+ i 1))))))))))))) :pattern (
  (compare1 a a_first a_last b b_first b_last)) ))))

(declare-fun dummy3 () (Array Int byte_t))

(declare-fun value__size1 () Int)

(declare-fun object__size1 ((Array Int byte_t)) Int)

;; value__size_axiom
  (assert (<= 0 value__size1))

;; object__size_axiom
  (assert (forall ((a (Array Int byte_t))) (<= 0 (object__size1 a))))

(declare-fun user_eq3 ((Array Int byte_t) (Array Int byte_t)) Bool)

;; compare_def
  (assert
  (forall ((a (Array Int byte_t)) (b (Array Int byte_t)))
  (forall ((a_first Int) (a_last Int) (b_first Int) (b_last Int))
  (! (and
     (= (= (compare1 a a_first a_last b b_first b_last) 0)
     (= (bool_eq2 a a_first a_last b b_first b_last) true))
     (and
     (= (< (compare1 a a_first a_last b b_first b_last) 0)
     (exists ((i Int) (j Int))
     (and (<= i a_last)
     (and (< j b_last)
     (and (= (bool_eq2 a a_first i b b_first j) true)
     (or (= i a_last)
     (and (< i a_last)
     (bvult (to_rep1 (select a (+ i 1))) (to_rep1 (select b (+ j 1)))))))))))
     (= (< 0 (compare1 a a_first a_last b b_first b_last))
     (exists ((i Int) (j Int))
     (and (<= i b_last)
     (and (< j a_last)
     (and (= (bool_eq2 a a_first j b b_first i) true)
     (or (= i b_last)
     (and (< i b_last)
     (bvugt (to_rep1 (select a (+ j 1))) (to_rep1 (select b (+ i 1))))))))))))) :pattern (
  (compare1 a a_first a_last b b_first b_last)) ))))

(declare-fun dummy4 () (Array Int byte_t))

(declare-fun value__size2 () Int)

(declare-fun object__size2 ((Array Int byte_t)) Int)

;; value__size_axiom
  (assert (<= 0 value__size2))

;; object__size_axiom
  (assert (forall ((a (Array Int byte_t))) (<= 0 (object__size2 a))))

(declare-fun user_eq4 ((Array Int byte_t) (Array Int byte_t)) Bool)

;; compare_def
  (assert
  (forall ((a (Array Int byte_t)) (b (Array Int byte_t)))
  (forall ((a_first Int) (a_last Int) (b_first Int) (b_last Int))
  (! (and
     (= (= (compare1 a a_first a_last b b_first b_last) 0)
     (= (bool_eq2 a a_first a_last b b_first b_last) true))
     (and
     (= (< (compare1 a a_first a_last b b_first b_last) 0)
     (exists ((i Int) (j Int))
     (and (<= i a_last)
     (and (< j b_last)
     (and (= (bool_eq2 a a_first i b b_first j) true)
     (or (= i a_last)
     (and (< i a_last)
     (bvult (to_rep1 (select a (+ i 1))) (to_rep1 (select b (+ j 1)))))))))))
     (= (< 0 (compare1 a a_first a_last b b_first b_last))
     (exists ((i Int) (j Int))
     (and (<= i b_last)
     (and (< j a_last)
     (and (= (bool_eq2 a a_first j b b_first i) true)
     (or (= i b_last)
     (and (< i b_last)
     (bvugt (to_rep1 (select a (+ j 1))) (to_rep1 (select b (+ i 1))))))))))))) :pattern (
  (compare1 a a_first a_last b b_first b_last)) ))))

(declare-fun nullbytearray () (Array Int byte_t))

(declare-fun temp___standard__wibble_0 ((_ BitVec 8)) (Array Int byte_t))

;; def_axiom
  (assert
  (forall ((temp___standard__wibble_2 (_ BitVec 8)))
  (! (forall ((temp___standard__wibble_3 Int))
     (= (select (temp___standard__wibble_0 temp___standard__wibble_2) temp___standard__wibble_3)
     (of_rep1 temp___standard__wibble_2))) :pattern ((temp___standard__wibble_0
                                                     temp___standard__wibble_2)) )))

(declare-fun a () us_t2)

(declare-fun b () us_t2)

(define-fun dynamic_property1 ((first_int Int) (last_int Int)
  (x Int)) Bool (and (<= first_int x) (<= x last_int)))

(define-fun bool_eq5 ((x Int) (y Int)) Bool (ite (= x y) true false))

(declare-fun attr__ATTRIBUTE_IMAGE3 (Int) uni)

;; attr__ATTRIBUTE_IMAGE_sort
  (assert (forall ((x Int)) (sort us_image (attr__ATTRIBUTE_IMAGE3 x))))

(declare-fun attr__ATTRIBUTE_VALUE__pre_check3 (uni) Bool)

(declare-fun attr__ATTRIBUTE_VALUE3 (uni) Int)

(declare-fun user_eq5 (integer integer) Bool)

(declare-fun dummy5 () integer)

(declare-fun first2 (t2) integer)

(declare-fun last2 (t2) integer)

(declare-fun mk1 (Int Int) t2)

;; mk_def
  (assert
  (forall ((f Int) (l Int))
  (! (=> (in_range1 f)
     (=> (in_range1 l)
     (and (= (to_rep (first2 (mk1 f l))) f) (= (to_rep (last2 (mk1 f l))) l)))) :pattern (
  (mk1 f l)) )))

(define-fun dynamic_property2 ((range_first Int) (range_last Int) (low Int)
  (high Int)) Bool (and (in_range1 low)
                   (and (in_range1 high)
                   (=> (<= low high)
                   (and (dynamic_property1 range_first range_last low)
                   (dynamic_property1 range_first range_last high))))))

(declare-fun mk___t1 ((Array Int byte_t) t2) us_t)

(declare-fun elts1 (us_t) (Array Int byte_t))

;; elts_def
  (assert
  (forall ((u (Array Int byte_t)) (u1 t2)) (= (elts1 (mk___t1 u u1)) u)))

(declare-fun rt1 (us_t) t2)

;; rt_def
  (assert
  (forall ((u (Array Int byte_t)) (u1 t2)) (= (rt1 (mk___t1 u u1)) u1)))

(define-fun of_array1 ((a1 (Array Int byte_t)) (f Int)
  (l Int)) us_t (mk___t1 a1 (mk1 f l)))

(define-fun first3 ((a1 us_t)) Int (to_rep (first2 (rt1 a1))))

(define-fun last3 ((a1 us_t)) Int (to_rep (last2 (rt1 a1))))

(define-fun length1 ((a1 us_t)) Int (ite (<= (first3 a1) (last3 a1))
                                    (+ (- (last3 a1) (first3 a1)) 1) 0))

(declare-fun value__size3 () Int)

(declare-fun object__size3 ((Array Int byte_t)) Int)

;; value__size_axiom
  (assert (<= 0 value__size3))

;; object__size_axiom
  (assert (forall ((a1 (Array Int byte_t))) (<= 0 (object__size3 a1))))

(define-fun bool_eq6 ((x us_t)
  (y us_t)) Bool (bool_eq2 (elts1 x) (to_rep (first2 (rt1 x)))
                 (to_rep (last2 (rt1 x))) (elts1 y) (to_rep (first2 (rt1 y)))
                 (to_rep (last2 (rt1 y)))))

(declare-fun user_eq6 (us_t us_t) Bool)

(declare-fun dummy6 () us_t)

;; compare_def
  (assert
  (forall ((a1 (Array Int byte_t)) (b1 (Array Int byte_t)))
  (forall ((a_first Int) (a_last Int) (b_first Int) (b_last Int))
  (! (and
     (= (= (compare1 a1 a_first a_last b1 b_first b_last) 0)
     (= (bool_eq2 a1 a_first a_last b1 b_first b_last) true))
     (and
     (= (< (compare1 a1 a_first a_last b1 b_first b_last) 0)
     (exists ((i Int) (j Int))
     (and (<= i a_last)
     (and (< j b_last)
     (and (= (bool_eq2 a1 a_first i b1 b_first j) true)
     (or (= i a_last)
     (and (< i a_last)
     (bvult (to_rep1 (select a1 (+ i 1))) (to_rep1 (select b1 (+ j 1)))))))))))
     (= (< 0 (compare1 a1 a_first a_last b1 b_first b_last))
     (exists ((i Int) (j Int))
     (and (<= i b_last)
     (and (< j a_last)
     (and (= (bool_eq2 a1 a_first j b1 b_first i) true)
     (or (= i b_last)
     (and (< i b_last)
     (bvugt (to_rep1 (select a1 (+ j 1))) (to_rep1 (select b1 (+ i 1))))))))))))) :pattern (
  (compare1 a1 a_first a_last b1 b_first b_last)) ))))

(declare-fun ret__first () integer)

(declare-fun ret__last () integer)

(declare-fun attr__ATTRIBUTE_ADDRESS () Int)

(define-fun dynamic_property3 ((first_int Int) (last_int Int)
  (x Int)) Bool (and (<= first_int x) (<= x last_int)))

(define-fun bool_eq7 ((x Int) (y Int)) Bool (ite (= x y) true false))

(declare-fun attr__ATTRIBUTE_IMAGE4 (Int) uni)

;; attr__ATTRIBUTE_IMAGE_sort
  (assert (forall ((x Int)) (sort us_image (attr__ATTRIBUTE_IMAGE4 x))))

(declare-fun attr__ATTRIBUTE_VALUE__pre_check4 (uni) Bool)

(declare-fun attr__ATTRIBUTE_VALUE4 (uni) Int)

(declare-fun user_eq7 (integer integer) Bool)

(declare-fun dummy7 () integer)

(declare-fun first4 (t) integer)

(declare-fun last4 (t) integer)

(declare-fun mk2 (Int Int) t)

;; mk_def
  (assert
  (forall ((f Int) (l Int))
  (! (=> (in_range1 f)
     (=> (in_range1 l)
     (and (= (to_rep (first4 (mk2 f l))) f) (= (to_rep (last4 (mk2 f l))) l)))) :pattern (
  (mk2 f l)) )))

(define-fun dynamic_property4 ((range_first Int) (range_last Int) (low Int)
  (high Int)) Bool (and (in_range1 low)
                   (and (in_range1 high)
                   (=> (<= low high)
                   (and (dynamic_property3 range_first range_last low)
                   (dynamic_property3 range_first range_last high))))))

(declare-sort us_t4 0)

(declare-fun us_t5 () ty)

(declare-fun mk___t2 ((Array Int byte_t) t) us_t4)

(declare-fun elts2 (us_t4) (Array Int byte_t))

;; elts_def
  (assert
  (forall ((u (Array Int byte_t)) (u1 t)) (= (elts2 (mk___t2 u u1)) u)))

(declare-fun rt2 (us_t4) t)

;; rt_def
  (assert
  (forall ((u (Array Int byte_t)) (u1 t)) (= (rt2 (mk___t2 u u1)) u1)))

(define-fun of_array2 ((a1 (Array Int byte_t)) (f Int)
  (l Int)) us_t4 (mk___t2 a1 (mk2 f l)))

(define-fun first5 ((a1 us_t4)) Int (to_rep (first4 (rt2 a1))))

(define-fun last5 ((a1 us_t4)) Int (to_rep (last4 (rt2 a1))))

(define-fun length2 ((a1 us_t4)) Int (ite (<= (first5 a1) (last5 a1))
                                     (+ (- (last5 a1) (first5 a1)) 1) 0))

(declare-fun value__size4 () Int)

(declare-fun object__size4 ((Array Int byte_t)) Int)

;; value__size_axiom
  (assert (<= 0 value__size4))

;; object__size_axiom
  (assert (forall ((a1 (Array Int byte_t))) (<= 0 (object__size4 a1))))

(define-fun bool_eq8 ((x us_t4)
  (y us_t4)) Bool (bool_eq2 (elts2 x) (to_rep (first4 (rt2 x)))
                  (to_rep (last4 (rt2 x))) (elts2 y)
                  (to_rep (first4 (rt2 y))) (to_rep (last4 (rt2 y)))))

(declare-fun user_eq8 (us_t4 us_t4) Bool)

(declare-fun dummy8 () us_t4)

;; compare_def
  (assert
  (forall ((a1 (Array Int byte_t)) (b1 (Array Int byte_t)))
  (forall ((a_first Int) (a_last Int) (b_first Int) (b_last Int))
  (! (and
     (= (= (compare1 a1 a_first a_last b1 b_first b_last) 0)
     (= (bool_eq2 a1 a_first a_last b1 b_first b_last) true))
     (and
     (= (< (compare1 a1 a_first a_last b1 b_first b_last) 0)
     (exists ((i Int) (j Int))
     (and (<= i a_last)
     (and (< j b_last)
     (and (= (bool_eq2 a1 a_first i b1 b_first j) true)
     (or (= i a_last)
     (and (< i a_last)
     (bvult (to_rep1 (select a1 (+ i 1))) (to_rep1 (select b1 (+ j 1)))))))))))
     (= (< 0 (compare1 a1 a_first a_last b1 b_first b_last))
     (exists ((i Int) (j Int))
     (and (<= i b_last)
     (and (< j a_last)
     (and (= (bool_eq2 a1 a_first j b1 b_first i) true)
     (or (= i b_last)
     (and (< i b_last)
     (bvugt (to_rep1 (select a1 (+ j 1))) (to_rep1 (select b1 (+ i 1))))))))))))) :pattern (
  (compare1 a1 a_first a_last b1 b_first b_last)) ))))

(define-fun dynamic_property5 ((first_int Int) (last_int Int)
  (x Int)) Bool (and (<= first_int x) (<= x last_int)))

(define-fun bool_eq9 ((x Int) (y Int)) Bool (ite (= x y) true false))

(declare-fun attr__ATTRIBUTE_IMAGE5 (Int) uni)

;; attr__ATTRIBUTE_IMAGE_sort
  (assert (forall ((x Int)) (sort us_image (attr__ATTRIBUTE_IMAGE5 x))))

(declare-fun attr__ATTRIBUTE_VALUE__pre_check5 (uni) Bool)

(declare-fun attr__ATTRIBUTE_VALUE5 (uni) Int)

(declare-fun user_eq9 (integer integer) Bool)

(declare-fun dummy9 () integer)

(declare-sort t7 0)

(declare-fun t8 () ty)

(declare-fun first6 (t7) integer)

(declare-fun last6 (t7) integer)

(declare-fun mk3 (Int Int) t7)

;; mk_def
  (assert
  (forall ((f Int) (l Int))
  (! (=> (in_range1 f)
     (=> (in_range1 l)
     (and (= (to_rep (first6 (mk3 f l))) f) (= (to_rep (last6 (mk3 f l))) l)))) :pattern (
  (mk3 f l)) )))

(define-fun dynamic_property6 ((range_first Int) (range_last Int) (low Int)
  (high Int)) Bool (and (in_range1 low)
                   (and (in_range1 high)
                   (=> (<= low high)
                   (and (dynamic_property5 range_first range_last low)
                   (dynamic_property5 range_first range_last high))))))

(declare-sort us_t6 0)

(declare-fun us_t7 () ty)

(declare-fun mk___t3 ((Array Int byte_t) t7) us_t6)

(declare-fun elts3 (us_t6) (Array Int byte_t))

;; elts_def
  (assert
  (forall ((u (Array Int byte_t)) (u1 t7)) (= (elts3 (mk___t3 u u1)) u)))

(declare-fun rt3 (us_t6) t7)

;; rt_def
  (assert
  (forall ((u (Array Int byte_t)) (u1 t7)) (= (rt3 (mk___t3 u u1)) u1)))

(define-fun of_array3 ((a1 (Array Int byte_t)) (f Int)
  (l Int)) us_t6 (mk___t3 a1 (mk3 f l)))

(define-fun first7 ((a1 us_t6)) Int (to_rep (first6 (rt3 a1))))

(define-fun last7 ((a1 us_t6)) Int (to_rep (last6 (rt3 a1))))

(define-fun length3 ((a1 us_t6)) Int (ite (<= (first7 a1) (last7 a1))
                                     (+ (- (last7 a1) (first7 a1)) 1) 0))

(declare-fun value__size5 () Int)

(declare-fun object__size5 ((Array Int byte_t)) Int)

;; value__size_axiom
  (assert (<= 0 value__size5))

;; object__size_axiom
  (assert (forall ((a1 (Array Int byte_t))) (<= 0 (object__size5 a1))))

(define-fun bool_eq10 ((x us_t6)
  (y us_t6)) Bool (bool_eq2 (elts3 x) (to_rep (first6 (rt3 x)))
                  (to_rep (last6 (rt3 x))) (elts3 y)
                  (to_rep (first6 (rt3 y))) (to_rep (last6 (rt3 y)))))

(declare-fun user_eq10 (us_t6 us_t6) Bool)

(declare-fun dummy10 () us_t6)

;; compare_def
  (assert
  (forall ((a1 (Array Int byte_t)) (b1 (Array Int byte_t)))
  (forall ((a_first Int) (a_last Int) (b_first Int) (b_last Int))
  (! (and
     (= (= (compare1 a1 a_first a_last b1 b_first b_last) 0)
     (= (bool_eq2 a1 a_first a_last b1 b_first b_last) true))
     (and
     (= (< (compare1 a1 a_first a_last b1 b_first b_last) 0)
     (exists ((i Int) (j Int))
     (and (<= i a_last)
     (and (< j b_last)
     (and (= (bool_eq2 a1 a_first i b1 b_first j) true)
     (or (= i a_last)
     (and (< i a_last)
     (bvult (to_rep1 (select a1 (+ i 1))) (to_rep1 (select b1 (+ j 1)))))))))))
     (= (< 0 (compare1 a1 a_first a_last b1 b_first b_last))
     (exists ((i Int) (j Int))
     (and (<= i b_last)
     (and (< j a_last)
     (and (= (bool_eq2 a1 a_first j b1 b_first i) true)
     (or (= i b_last)
     (and (< i b_last)
     (bvugt (to_rep1 (select a1 (+ j 1))) (to_rep1 (select b1 (+ i 1))))))))))))) :pattern (
  (compare1 a1 a_first a_last b1 b_first b_last)) ))))

;; nullbytearray__def_axiom
  (assert (= nullbytearray (temp___standard__wibble_0 ((_ int2bv 8) 0))))

(declare-fun o () Int)

(declare-fun o1 () Int)

(declare-fun o2 () Int)

(declare-fun o3 () Int)

(declare-fun o4 () Int)

(declare-fun o5 () Int)

(declare-fun temp___standard__wibble_93 () (Array Int byte_t))

(declare-fun temp___standard__wibble_931 () t4)

(declare-fun temp___standard__wibble_94 () (Array Int byte_t))

(declare-fun temp___standard__wibble_941 () t2)

(declare-fun o6 () (Array Int byte_t))

(declare-fun o7 () t2)

(declare-fun o8 () (Array Int byte_t))

(declare-fun ret () (Array Int byte_t))

;; H
  (assert (dynamic_property (- 2147483648) 2147483647 (to_rep (first (rt a)))
  (to_rep (last (rt a)))))

;; H
  (assert (dynamic_property (- 2147483648) 2147483647 (to_rep (first (rt b)))
  (to_rep (last (rt b)))))

;; H
  (assert (= (temp___standard__wibble_0 ((_ int2bv 8) 0)) nullbytearray))

;; H
  (assert
  (and
  (not
  (= (bool_eq2 (elts a) (to_rep (first (rt a))) (to_rep (last (rt a)))
     nullbytearray 1 0) true))
  (and
  (not
  (= (bool_eq2 (elts b) (to_rep (first (rt b))) (to_rep (last (rt b)))
     nullbytearray 1 0) true))
  (and (<= (length b) 2147483647)
  (and (<= (to_rep (last (rt a))) (- 2147483647 (length b)))
  (<= (- (length a) 1) (- 2147483647 (length b))))))))

;; H
  (assert
  (and (dynamic_property2 0 (+ (- (length a) 1) (length b))
  (to_rep ret__first) (to_rep ret__last))
  (and (= (to_rep ret__first) 0)
  (= (to_rep ret__last) (+ (- (length a) 1) (length b))))))

;; H
  (assert (=> (= (length a) 0) (= (elts b) temp___standard__wibble_93)))

;; H
  (assert
  (=> (= (length a) 0)
  (= (mk (to_rep (first (rt b))) (to_rep (last (rt b)))) temp___standard__wibble_931)))

;; H
  (assert
  (=> (not (= (length a) 0))
  (=> (<= (to_rep (first (rt b))) (to_rep (last (rt b))))
  (= o (+ (- (to_rep (last (rt b))) (to_rep (first (rt b)))) 1)))))

;; H
  (assert
  (=> (not (= (length a) 0))
  (=> (not (<= (to_rep (first (rt b))) (to_rep (last (rt b))))) (= o 0))))

;; H
  (assert
  (=> (not (= (length a) 0))
  (=> (<= (to_rep (first (rt a))) (to_rep (last (rt a))))
  (= o1 (+ (- (to_rep (last (rt a))) (to_rep (first (rt a)))) 1)))))

;; H
  (assert
  (=> (not (= (length a) 0))
  (=> (not (<= (to_rep (first (rt a))) (to_rep (last (rt a))))) (= o1 0))))

;; H
  (assert (=> (not (= (length a) 0)) (= o2 (+ o1 o))))

;; H
  (assert (=> (not (= (length a) 0)) (= o3 (+ (to_rep (first (rt a))) o2))))

;; H
  (assert (=> (not (= (length a) 0)) (= o4 (- o3 1))))

;; H
  (assert (=> (not (= (length a) 0)) (and (= o5 o4) (in_range1 o4))))

;; H
  (assert
  (=> (not (= (length a) 0))
  (= (concat2 (elts a) (to_rep (first (rt a))) (to_rep (last (rt a)))
     (elts b) (to_rep (first (rt b))) (to_rep (last (rt b)))) temp___standard__wibble_93)))

;; H
  (assert
  (=> (not (= (length a) 0))
  (= (mk (to_rep (first (rt a))) o5) temp___standard__wibble_931)))

;; H
  (assert
  (= (ite (<= (to_rep (first temp___standard__wibble_931)) (to_rep
                                                           (last
                                                           temp___standard__wibble_931)))
     (+ (- (to_rep (last temp___standard__wibble_931)) (to_rep
                                                       (first
                                                       temp___standard__wibble_931))) 1)
     0) (ite (<= 0 (+ (- (length a) 1) (length b)))
        (+ (- (+ (- (length a) 1) (length b)) 0) 1) 0)))

;; H
  (assert
  (= (slide1 temp___standard__wibble_93
     (to_rep (first temp___standard__wibble_931)) 0) temp___standard__wibble_94))

;; H
  (assert
  (= (mk1 0 (+ (- (length a) 1) (length b))) temp___standard__wibble_941))

;; H
  (assert
  (= (ite (<= (to_rep (first2 temp___standard__wibble_941)) (to_rep
                                                            (last2
                                                            temp___standard__wibble_941)))
     (+ (- (to_rep (last2 temp___standard__wibble_941)) (to_rep
                                                        (first2
                                                        temp___standard__wibble_941))) 1)
     0) (ite (<= (to_rep ret__first) (to_rep ret__last))
        (+ (- (to_rep ret__last) (to_rep ret__first)) 1) 0)))

;; H
  (assert
  (= (mk___t1 o6 o7) (mk___t1 temp___standard__wibble_94
                     temp___standard__wibble_941)))

;; H
  (assert (= o8 o6))

;; H
  (assert (= ret o8))

(assert
  (not
  (= (bool_eq2 ret (to_rep (first4 (mk2 0 (- (length a) 1))))
     (to_rep (last4 (mk2 0 (- (length a) 1)))) (elts a)
     (to_rep (first (rt a))) (to_rep (last (rt a)))) true)))
(check-sat)
(exit)
