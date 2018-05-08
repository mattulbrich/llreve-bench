;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((dest$1_0 Int)
    (src$1_0 Int)
    (size$1_0 Int)
    (HEAP$1 (Array Int Int))
    (dest$2_0 Int)
    (src$2_0 Int)
    (size$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= dest$1_0 dest$2_0)
      (= src$1_0 src$2_0)
      (= size$1_0 size$2_0)
      (= HEAP$1 HEAP$2)))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= result$1 result$2)
      (= HEAP$1 HEAP$2)))
; :annot (INV_MAIN_42 dest$1_0 i.0$1_0 size$1_0 src$1_0 HEAP$1 dest.addr.0$2_0 size$2_0 src$2_0 src.addr.0$2_0 HEAP$2)
(declare-fun
   INV_MAIN_42
   (Int
    Int
    Int
    Int
    (Array Int Int)
    Int
    Int
    Int
    Int
    (Array Int Int))
   Bool)
(assert
   (forall
      ((dest$1_0_old Int)
       (src$1_0_old Int)
       (size$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dest$2_0_old Int)
       (src$2_0_old Int)
       (size$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dest$1_0_old src$1_0_old size$1_0_old HEAP$1_old dest$2_0_old src$2_0_old size$2_0_old HEAP$2_old)
         (let
            ((dest$1_0 dest$1_0_old)
             (src$1_0 src$1_0_old)
             (size$1_0 size$1_0_old)
             (HEAP$1 HEAP$1_old)
             (i.0$1_0 0)
             (dest$2_0 dest$2_0_old)
             (src$2_0 src$2_0_old))
            (let
               ((size$2_0 size$2_0_old)
                (HEAP$2 HEAP$2_old)
                (src.addr.0$2_0 src$2_0)
                (dest.addr.0$2_0 dest$2_0))
               (INV_MAIN_42 dest$1_0 i.0$1_0 size$1_0 src$1_0 HEAP$1 dest.addr.0$2_0 size$2_0 src$2_0 src.addr.0$2_0 HEAP$2))))))
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dest.addr.0$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int)
       (src.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old HEAP$1_old dest.addr.0$2_0_old size$2_0_old src$2_0_old src.addr.0$2_0_old HEAP$2_old)
         (let
            ((dest$1_0 dest$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (size$1_0 size$1_0_old))
            (let
               ((src$1_0 src$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 size$1_0)))
               (=>
                  (not cmp$1_0)
                  (let
                     ((result$1 1)
                      (HEAP$1_res HEAP$1)
                      (dest.addr.0$2_0 dest.addr.0$2_0_old)
                      (size$2_0 size$2_0_old)
                      (src$2_0 src$2_0_old)
                      (src.addr.0$2_0 src.addr.0$2_0_old))
                     (let
                        ((HEAP$2 HEAP$2_old)
                         (sub.ptr.lhs.cast$2_0 src.addr.0$2_0)
                         (sub.ptr.rhs.cast$2_0 src$2_0))
                        (let
                           ((sub.ptr.sub$2_0 (- sub.ptr.lhs.cast$2_0 sub.ptr.rhs.cast$2_0)))
                           (let
                              ((sub.ptr.div$2_0 (div sub.ptr.sub$2_0 4))
                               (conv$2_0 size$2_0))
                              (let
                                 ((cmp$2_0 (< sub.ptr.div$2_0 conv$2_0)))
                                 (=>
                                    (not cmp$2_0)
                                    (let
                                       ((result$2 1)
                                        (HEAP$2_res HEAP$2))
                                       (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dest.addr.0$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int)
       (src.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old HEAP$1_old dest.addr.0$2_0_old size$2_0_old src$2_0_old src.addr.0$2_0_old HEAP$2_old)
         (let
            ((dest$1_0 dest$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (size$1_0 size$1_0_old))
            (let
               ((src$1_0 src$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 size$1_0)))
               (=>
                  cmp$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ src$1_0 (* 4 idxprom$1_0))))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0))
                            (idxprom1$1_0 i.0$1_0))
                           (let
                              ((arrayidx2$1_0 (+ dest$1_0 (* 4 idxprom1$1_0))))
                              (let
                                 ((HEAP$1 (store HEAP$1 arrayidx2$1_0 _$1_0))
                                  (inc$1_0 (+ i.0$1_0 1)))
                                 (let
                                    ((i.0$1_0 inc$1_0)
                                     (dest.addr.0$2_0 dest.addr.0$2_0_old)
                                     (size$2_0 size$2_0_old)
                                     (src$2_0 src$2_0_old)
                                     (src.addr.0$2_0 src.addr.0$2_0_old))
                                    (let
                                       ((HEAP$2 HEAP$2_old)
                                        (sub.ptr.lhs.cast$2_0 src.addr.0$2_0)
                                        (sub.ptr.rhs.cast$2_0 src$2_0))
                                       (let
                                          ((sub.ptr.sub$2_0 (- sub.ptr.lhs.cast$2_0 sub.ptr.rhs.cast$2_0)))
                                          (let
                                             ((sub.ptr.div$2_0 (div sub.ptr.sub$2_0 4))
                                              (conv$2_0 size$2_0))
                                             (let
                                                ((cmp$2_0 (< sub.ptr.div$2_0 conv$2_0)))
                                                (=>
                                                   cmp$2_0
                                                   (let
                                                      ((_$2_0 (select HEAP$2 src.addr.0$2_0)))
                                                      (let
                                                         ((HEAP$2 (store HEAP$2 dest.addr.0$2_0 _$2_0))
                                                          (incdec.ptr$2_0 (+ dest.addr.0$2_0 (* 4 1)))
                                                          (incdec.ptr2$2_0 (+ src.addr.0$2_0 (* 4 1))))
                                                         (let
                                                            ((src.addr.0$2_0 incdec.ptr2$2_0)
                                                             (dest.addr.0$2_0 incdec.ptr$2_0))
                                                            (INV_MAIN_42 dest$1_0 i.0$1_0 size$1_0 src$1_0 HEAP$1 dest.addr.0$2_0 size$2_0 src$2_0 src.addr.0$2_0 HEAP$2)))))))))))))))))))))
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dest.addr.0$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int)
       (src.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old HEAP$1_old dest.addr.0$2_0_old size$2_0_old src$2_0_old src.addr.0$2_0_old HEAP$2_old)
         (let
            ((dest$1_0 dest$1_0_old)
             (i.0$1_0 i.0$1_0_old)
             (size$1_0 size$1_0_old))
            (let
               ((src$1_0 src$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp$1_0 (< i.0$1_0 size$1_0)))
               (=>
                  cmp$1_0
                  (let
                     ((idxprom$1_0 i.0$1_0))
                     (let
                        ((arrayidx$1_0 (+ src$1_0 (* 4 idxprom$1_0))))
                        (let
                           ((_$1_0 (select HEAP$1 arrayidx$1_0))
                            (idxprom1$1_0 i.0$1_0))
                           (let
                              ((arrayidx2$1_0 (+ dest$1_0 (* 4 idxprom1$1_0))))
                              (let
                                 ((HEAP$1 (store HEAP$1 arrayidx2$1_0 _$1_0))
                                  (inc$1_0 (+ i.0$1_0 1)))
                                 (let
                                    ((i.0$1_0 inc$1_0))
                                    (=>
                                       (let
                                          ((dest.addr.0$2_0 dest.addr.0$2_0_old)
                                           (size$2_0 size$2_0_old)
                                           (src$2_0 src$2_0_old)
                                           (src.addr.0$2_0 src.addr.0$2_0_old))
                                          (let
                                             ((HEAP$2 HEAP$2_old)
                                              (sub.ptr.lhs.cast$2_0 src.addr.0$2_0)
                                              (sub.ptr.rhs.cast$2_0 src$2_0))
                                             (let
                                                ((sub.ptr.sub$2_0 (- sub.ptr.lhs.cast$2_0 sub.ptr.rhs.cast$2_0)))
                                                (let
                                                   ((sub.ptr.div$2_0 (div sub.ptr.sub$2_0 4))
                                                    (conv$2_0 size$2_0))
                                                   (let
                                                      ((cmp$2_0 (< sub.ptr.div$2_0 conv$2_0)))
                                                      (=>
                                                         cmp$2_0
                                                         (let
                                                            ((_$2_0 (select HEAP$2 src.addr.0$2_0)))
                                                            (let
                                                               ((HEAP$2 (store HEAP$2 dest.addr.0$2_0 _$2_0))
                                                                (incdec.ptr$2_0 (+ dest.addr.0$2_0 (* 4 1)))
                                                                (incdec.ptr2$2_0 (+ src.addr.0$2_0 (* 4 1))))
                                                               (let
                                                                  ((src.addr.0$2_0 incdec.ptr2$2_0)
                                                                   (dest.addr.0$2_0 incdec.ptr$2_0))
                                                                  false)))))))))
                                       (INV_MAIN_42 dest$1_0 i.0$1_0 size$1_0 src$1_0 HEAP$1 dest.addr.0$2_0_old size$2_0_old src$2_0_old src.addr.0$2_0_old HEAP$2_old))))))))))))))
(assert
   (forall
      ((dest$1_0_old Int)
       (i.0$1_0_old Int)
       (size$1_0_old Int)
       (src$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dest.addr.0$2_0_old Int)
       (size$2_0_old Int)
       (src$2_0_old Int)
       (src.addr.0$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old HEAP$1_old dest.addr.0$2_0_old size$2_0_old src$2_0_old src.addr.0$2_0_old HEAP$2_old)
         (let
            ((dest.addr.0$2_0 dest.addr.0$2_0_old)
             (size$2_0 size$2_0_old)
             (src$2_0 src$2_0_old)
             (src.addr.0$2_0 src.addr.0$2_0_old))
            (let
               ((HEAP$2 HEAP$2_old)
                (sub.ptr.lhs.cast$2_0 src.addr.0$2_0)
                (sub.ptr.rhs.cast$2_0 src$2_0))
               (let
                  ((sub.ptr.sub$2_0 (- sub.ptr.lhs.cast$2_0 sub.ptr.rhs.cast$2_0)))
                  (let
                     ((sub.ptr.div$2_0 (div sub.ptr.sub$2_0 4))
                      (conv$2_0 size$2_0))
                     (let
                        ((cmp$2_0 (< sub.ptr.div$2_0 conv$2_0)))
                        (=>
                           cmp$2_0
                           (let
                              ((_$2_0 (select HEAP$2 src.addr.0$2_0)))
                              (let
                                 ((HEAP$2 (store HEAP$2 dest.addr.0$2_0 _$2_0))
                                  (incdec.ptr$2_0 (+ dest.addr.0$2_0 (* 4 1)))
                                  (incdec.ptr2$2_0 (+ src.addr.0$2_0 (* 4 1))))
                                 (let
                                    ((src.addr.0$2_0 incdec.ptr2$2_0)
                                     (dest.addr.0$2_0 incdec.ptr$2_0))
                                    (=>
                                       (let
                                          ((dest$1_0 dest$1_0_old)
                                           (i.0$1_0 i.0$1_0_old)
                                           (size$1_0 size$1_0_old))
                                          (let
                                             ((src$1_0 src$1_0_old)
                                              (HEAP$1 HEAP$1_old)
                                              (cmp$1_0 (< i.0$1_0 size$1_0)))
                                             (=>
                                                cmp$1_0
                                                (let
                                                   ((idxprom$1_0 i.0$1_0))
                                                   (let
                                                      ((arrayidx$1_0 (+ src$1_0 (* 4 idxprom$1_0))))
                                                      (let
                                                         ((_$1_0 (select HEAP$1 arrayidx$1_0))
                                                          (idxprom1$1_0 i.0$1_0))
                                                         (let
                                                            ((arrayidx2$1_0 (+ dest$1_0 (* 4 idxprom1$1_0))))
                                                            (let
                                                               ((HEAP$1 (store HEAP$1 arrayidx2$1_0 _$1_0))
                                                                (inc$1_0 (+ i.0$1_0 1)))
                                                               (let
                                                                  ((i.0$1_0 inc$1_0))
                                                                  false)))))))))
                                       (INV_MAIN_42 dest$1_0_old i.0$1_0_old size$1_0_old src$1_0_old HEAP$1_old dest.addr.0$2_0 size$2_0 src$2_0 src.addr.0$2_0 HEAP$2))))))))))))))
(check-sat)
(get-model)
