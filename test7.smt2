(set-logic ALL)
(set-option :produce-models true)
(set-info :smt-lib-version 2.6)

;; simple sort
(declare-sort A 0)

;; parametric sort
(declare-sort B 2)

;; partial refinement
(define-sort C (x) (B x Int))

;; full refinement
(define-sort D () (B Bool Int))
(define-sort E () (C Bool))

;; using an indexed sort
(define-sort F () (_ BitVec 4))

;; using user-defined sorts
(define-sort G () (B A F))
(define-sort H () A)

;; useless parameters
(define-sort I (x y) (B x Int))

;; datatypes


(declare-const a A)
(declare-const b (B Bool Int))
(declare-const c (C Bool))
(declare-const d D)
(declare-const e E)
(declare-const f F)
(declare-const g G)
(declare-const h H)
(declare-const i (I Bool Float32))

(assert (distinct b c d e i))
(assert (distinct a h))

;; not legal:
;;(declare-const b B)
;;(declare-const c C)
