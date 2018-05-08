;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((dst0$1_0 Int)
    (src0$1_0 Int)
    (length$1_0 Int)
    (HEAP$1 (Array Int Int))
    (dst$2_0 Int)
    (src$2_0 Int)
    (count$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= dst0$1_0 dst$2_0)
      (= src0$1_0 src$2_0)
      (= length$1_0 count$2_0)
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
; :annot (INV_MAIN_0 dst.0$1_0 dst0$1_0 src.0$1_0 t.0$1_0 HEAP$1 a.0$2_0 b.0$2_0 dec$2_0 dst$2_0 HEAP$2)
(declare-fun
   INV_MAIN_0
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
; :annot (INV_MAIN_1 dst.1$1_0 dst0$1_0 src.1$1_0 t.1$1_0 HEAP$1 a.1$2_0 b.1$2_0 dec7$2_0 dst$2_0 HEAP$2)
(declare-fun
   INV_MAIN_1
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
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     or.cond$1_0
                     (let
                        ((result$1 dst0$1_0)
                         (HEAP$1_res HEAP$1)
                         (dst$2_0 dst$2_0_old)
                         (src$2_0 src$2_0_old))
                        (let
                           ((count$2_0 count$2_0_old)
                            (HEAP$2 HEAP$2_old)
                            (cmp$2_0 (distinct src$2_0 dst$2_0)))
                           (=>
                              cmp$2_0
                              (let
                                 ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                 (=>
                                    cmp1$2_0
                                    (let
                                       ((count.addr.0$2_0 count$2_0))
                                       (let
                                          ((a.0$2_0 dst$2_0)
                                           (b.0$2_0 src$2_0)
                                           (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                           (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                          (not tobool$2_0)))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              cmp2$1_0
                              (let
                                 ((tobool$1_0 (distinct length$1_0 0)))
                                 (=>
                                    (not tobool$1_0)
                                    (let
                                       ((result$1 dst0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   cmp1$2_0
                                                   (let
                                                      ((count.addr.0$2_0 count$2_0))
                                                      (let
                                                         ((a.0$2_0 dst$2_0)
                                                          (b.0$2_0 src$2_0)
                                                          (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                                          (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                                         (not tobool$2_0))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              (not cmp2$1_0)
                              (let
                                 ((add.ptr$1_0 (+ src0$1_0 length$1_0))
                                  (add.ptr8$1_0 (+ dst0$1_0 length$1_0))
                                  (tobool9$1_0 (distinct length$1_0 0)))
                                 (=>
                                    (not tobool9$1_0)
                                    (let
                                       ((result$1 dst0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   cmp1$2_0
                                                   (let
                                                      ((count.addr.0$2_0 count$2_0))
                                                      (let
                                                         ((a.0$2_0 dst$2_0)
                                                          (b.0$2_0 src$2_0)
                                                          (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                                          (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                                         (not tobool$2_0))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     or.cond$1_0
                     (let
                        ((result$1 dst0$1_0)
                         (HEAP$1_res HEAP$1)
                         (dst$2_0 dst$2_0_old)
                         (src$2_0 src$2_0_old))
                        (let
                           ((count$2_0 count$2_0_old)
                            (HEAP$2 HEAP$2_old)
                            (cmp$2_0 (distinct src$2_0 dst$2_0)))
                           (=>
                              cmp$2_0
                              (let
                                 ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                 (=>
                                    (not cmp1$2_0)
                                    (let
                                       ((sub$2_0 (- count$2_0 1)))
                                       (let
                                          ((add.ptr$2_0 (+ dst$2_0 sub$2_0))
                                           (sub4$2_0 (- count$2_0 1)))
                                          (let
                                             ((add.ptr5$2_0 (+ src$2_0 sub4$2_0))
                                              (count.addr.1$2_0 count$2_0))
                                             (let
                                                ((a.1$2_0 add.ptr$2_0)
                                                 (b.1$2_0 add.ptr5$2_0)
                                                 (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                                 (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                                (not tobool8$2_0)))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              cmp2$1_0
                              (let
                                 ((tobool$1_0 (distinct length$1_0 0)))
                                 (=>
                                    (not tobool$1_0)
                                    (let
                                       ((result$1 dst0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   (not cmp1$2_0)
                                                   (let
                                                      ((sub$2_0 (- count$2_0 1)))
                                                      (let
                                                         ((add.ptr$2_0 (+ dst$2_0 sub$2_0))
                                                          (sub4$2_0 (- count$2_0 1)))
                                                         (let
                                                            ((add.ptr5$2_0 (+ src$2_0 sub4$2_0))
                                                             (count.addr.1$2_0 count$2_0))
                                                            (let
                                                               ((a.1$2_0 add.ptr$2_0)
                                                                (b.1$2_0 add.ptr5$2_0)
                                                                (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                                                (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                                               (not tobool8$2_0))))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              (not cmp2$1_0)
                              (let
                                 ((add.ptr$1_0 (+ src0$1_0 length$1_0))
                                  (add.ptr8$1_0 (+ dst0$1_0 length$1_0))
                                  (tobool9$1_0 (distinct length$1_0 0)))
                                 (=>
                                    (not tobool9$1_0)
                                    (let
                                       ((result$1 dst0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   (not cmp1$2_0)
                                                   (let
                                                      ((sub$2_0 (- count$2_0 1)))
                                                      (let
                                                         ((add.ptr$2_0 (+ dst$2_0 sub$2_0))
                                                          (sub4$2_0 (- count$2_0 1)))
                                                         (let
                                                            ((add.ptr5$2_0 (+ src$2_0 sub4$2_0))
                                                             (count.addr.1$2_0 count$2_0))
                                                            (let
                                                               ((a.1$2_0 add.ptr$2_0)
                                                                (b.1$2_0 add.ptr5$2_0)
                                                                (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                                                (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                                               (not tobool8$2_0))))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              cmp2$1_0
                              (let
                                 ((tobool$1_0 (distinct length$1_0 0)))
                                 (=>
                                    tobool$1_0
                                    (let
                                       ((dst.0$1_0 dst0$1_0)
                                        (src.0$1_0 src0$1_0)
                                        (t.0$1_0 length$1_0)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   cmp1$2_0
                                                   (let
                                                      ((count.addr.0$2_0 count$2_0))
                                                      (let
                                                         ((a.0$2_0 dst$2_0)
                                                          (b.0$2_0 src$2_0)
                                                          (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                                          (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                                         (=>
                                                            (not tobool$2_0)
                                                            (let
                                                               ((result$2 dst$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               false)))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              cmp2$1_0
                              (let
                                 ((tobool$1_0 (distinct length$1_0 0)))
                                 (=>
                                    tobool$1_0
                                    (let
                                       ((dst.0$1_0 dst0$1_0)
                                        (src.0$1_0 src0$1_0)
                                        (t.0$1_0 length$1_0)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   (not cmp1$2_0)
                                                   (let
                                                      ((sub$2_0 (- count$2_0 1)))
                                                      (let
                                                         ((add.ptr$2_0 (+ dst$2_0 sub$2_0))
                                                          (sub4$2_0 (- count$2_0 1)))
                                                         (let
                                                            ((add.ptr5$2_0 (+ src$2_0 sub4$2_0))
                                                             (count.addr.1$2_0 count$2_0))
                                                            (let
                                                               ((a.1$2_0 add.ptr$2_0)
                                                                (b.1$2_0 add.ptr5$2_0)
                                                                (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                                                (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                                               (=>
                                                                  (not tobool8$2_0)
                                                                  (let
                                                                     ((result$2 dst$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     false)))))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              cmp2$1_0
                              (let
                                 ((tobool$1_0 (distinct length$1_0 0)))
                                 (=>
                                    tobool$1_0
                                    (let
                                       ((dst.0$1_0 dst0$1_0)
                                        (src.0$1_0 src0$1_0)
                                        (t.0$1_0 length$1_0)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             (not cmp$2_0)
                                             (let
                                                ((result$2 dst$2_0)
                                                 (HEAP$2_res HEAP$2))
                                                false))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              cmp2$1_0
                              (let
                                 ((tobool$1_0 (distinct length$1_0 0)))
                                 (=>
                                    tobool$1_0
                                    (let
                                       ((dst.0$1_0 dst0$1_0)
                                        (src.0$1_0 src0$1_0)
                                        (t.0$1_0 length$1_0)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   (not cmp1$2_0)
                                                   (let
                                                      ((sub$2_0 (- count$2_0 1)))
                                                      (let
                                                         ((add.ptr$2_0 (+ dst$2_0 sub$2_0))
                                                          (sub4$2_0 (- count$2_0 1)))
                                                         (let
                                                            ((add.ptr5$2_0 (+ src$2_0 sub4$2_0))
                                                             (count.addr.1$2_0 count$2_0))
                                                            (let
                                                               ((a.1$2_0 add.ptr$2_0)
                                                                (b.1$2_0 add.ptr5$2_0)
                                                                (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                                                (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                                               (not tobool8$2_0))))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              (not cmp2$1_0)
                              (let
                                 ((add.ptr$1_0 (+ src0$1_0 length$1_0))
                                  (add.ptr8$1_0 (+ dst0$1_0 length$1_0))
                                  (tobool9$1_0 (distinct length$1_0 0)))
                                 (=>
                                    tobool9$1_0
                                    (let
                                       ((dst.1$1_0 add.ptr8$1_0)
                                        (src.1$1_0 add.ptr$1_0)
                                        (t.1$1_0 length$1_0)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   cmp1$2_0
                                                   (let
                                                      ((count.addr.0$2_0 count$2_0))
                                                      (let
                                                         ((a.0$2_0 dst$2_0)
                                                          (b.0$2_0 src$2_0)
                                                          (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                                          (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                                         (=>
                                                            (not tobool$2_0)
                                                            (let
                                                               ((result$2 dst$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               false)))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              (not cmp2$1_0)
                              (let
                                 ((add.ptr$1_0 (+ src0$1_0 length$1_0))
                                  (add.ptr8$1_0 (+ dst0$1_0 length$1_0))
                                  (tobool9$1_0 (distinct length$1_0 0)))
                                 (=>
                                    tobool9$1_0
                                    (let
                                       ((dst.1$1_0 add.ptr8$1_0)
                                        (src.1$1_0 add.ptr$1_0)
                                        (t.1$1_0 length$1_0)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   (not cmp1$2_0)
                                                   (let
                                                      ((sub$2_0 (- count$2_0 1)))
                                                      (let
                                                         ((add.ptr$2_0 (+ dst$2_0 sub$2_0))
                                                          (sub4$2_0 (- count$2_0 1)))
                                                         (let
                                                            ((add.ptr5$2_0 (+ src$2_0 sub4$2_0))
                                                             (count.addr.1$2_0 count$2_0))
                                                            (let
                                                               ((a.1$2_0 add.ptr$2_0)
                                                                (b.1$2_0 add.ptr5$2_0)
                                                                (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                                                (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                                               (=>
                                                                  (not tobool8$2_0)
                                                                  (let
                                                                     ((result$2 dst$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     false)))))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              (not cmp2$1_0)
                              (let
                                 ((add.ptr$1_0 (+ src0$1_0 length$1_0))
                                  (add.ptr8$1_0 (+ dst0$1_0 length$1_0))
                                  (tobool9$1_0 (distinct length$1_0 0)))
                                 (=>
                                    tobool9$1_0
                                    (let
                                       ((dst.1$1_0 add.ptr8$1_0)
                                        (src.1$1_0 add.ptr$1_0)
                                        (t.1$1_0 length$1_0)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             (not cmp$2_0)
                                             (let
                                                ((result$2 dst$2_0)
                                                 (HEAP$2_res HEAP$2))
                                                false))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              (not cmp2$1_0)
                              (let
                                 ((add.ptr$1_0 (+ src0$1_0 length$1_0))
                                  (add.ptr8$1_0 (+ dst0$1_0 length$1_0))
                                  (tobool9$1_0 (distinct length$1_0 0)))
                                 (=>
                                    tobool9$1_0
                                    (let
                                       ((dst.1$1_0 add.ptr8$1_0)
                                        (src.1$1_0 add.ptr$1_0)
                                        (t.1$1_0 length$1_0)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   cmp1$2_0
                                                   (let
                                                      ((count.addr.0$2_0 count$2_0))
                                                      (let
                                                         ((a.0$2_0 dst$2_0)
                                                          (b.0$2_0 src$2_0)
                                                          (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                                          (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                                         (not tobool$2_0))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     or.cond$1_0
                     (let
                        ((result$1 dst0$1_0)
                         (HEAP$1_res HEAP$1)
                         (dst$2_0 dst$2_0_old)
                         (src$2_0 src$2_0_old))
                        (let
                           ((count$2_0 count$2_0_old)
                            (HEAP$2 HEAP$2_old)
                            (cmp$2_0 (distinct src$2_0 dst$2_0)))
                           (=>
                              cmp$2_0
                              (let
                                 ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                 (=>
                                    cmp1$2_0
                                    (let
                                       ((count.addr.0$2_0 count$2_0))
                                       (let
                                          ((a.0$2_0 dst$2_0)
                                           (b.0$2_0 src$2_0)
                                           (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                           (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                          (=>
                                             (not tobool$2_0)
                                             (let
                                                ((result$2 dst$2_0)
                                                 (HEAP$2_res HEAP$2))
                                                (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     or.cond$1_0
                     (let
                        ((result$1 dst0$1_0)
                         (HEAP$1_res HEAP$1)
                         (dst$2_0 dst$2_0_old)
                         (src$2_0 src$2_0_old))
                        (let
                           ((count$2_0 count$2_0_old)
                            (HEAP$2 HEAP$2_old)
                            (cmp$2_0 (distinct src$2_0 dst$2_0)))
                           (=>
                              cmp$2_0
                              (let
                                 ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                 (=>
                                    (not cmp1$2_0)
                                    (let
                                       ((sub$2_0 (- count$2_0 1)))
                                       (let
                                          ((add.ptr$2_0 (+ dst$2_0 sub$2_0))
                                           (sub4$2_0 (- count$2_0 1)))
                                          (let
                                             ((add.ptr5$2_0 (+ src$2_0 sub4$2_0))
                                              (count.addr.1$2_0 count$2_0))
                                             (let
                                                ((a.1$2_0 add.ptr$2_0)
                                                 (b.1$2_0 add.ptr5$2_0)
                                                 (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                                 (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                                (=>
                                                   (not tobool8$2_0)
                                                   (let
                                                      ((result$2 dst$2_0)
                                                       (HEAP$2_res HEAP$2))
                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     or.cond$1_0
                     (let
                        ((result$1 dst0$1_0)
                         (HEAP$1_res HEAP$1)
                         (dst$2_0 dst$2_0_old)
                         (src$2_0 src$2_0_old))
                        (let
                           ((count$2_0 count$2_0_old)
                            (HEAP$2 HEAP$2_old)
                            (cmp$2_0 (distinct src$2_0 dst$2_0)))
                           (=>
                              (not cmp$2_0)
                              (let
                                 ((result$2 dst$2_0)
                                  (HEAP$2_res HEAP$2))
                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              cmp2$1_0
                              (let
                                 ((tobool$1_0 (distinct length$1_0 0)))
                                 (=>
                                    (not tobool$1_0)
                                    (let
                                       ((result$1 dst0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   cmp1$2_0
                                                   (let
                                                      ((count.addr.0$2_0 count$2_0))
                                                      (let
                                                         ((a.0$2_0 dst$2_0)
                                                          (b.0$2_0 src$2_0)
                                                          (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                                          (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                                         (=>
                                                            (not tobool$2_0)
                                                            (let
                                                               ((result$2 dst$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              cmp2$1_0
                              (let
                                 ((tobool$1_0 (distinct length$1_0 0)))
                                 (=>
                                    (not tobool$1_0)
                                    (let
                                       ((result$1 dst0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   (not cmp1$2_0)
                                                   (let
                                                      ((sub$2_0 (- count$2_0 1)))
                                                      (let
                                                         ((add.ptr$2_0 (+ dst$2_0 sub$2_0))
                                                          (sub4$2_0 (- count$2_0 1)))
                                                         (let
                                                            ((add.ptr5$2_0 (+ src$2_0 sub4$2_0))
                                                             (count.addr.1$2_0 count$2_0))
                                                            (let
                                                               ((a.1$2_0 add.ptr$2_0)
                                                                (b.1$2_0 add.ptr5$2_0)
                                                                (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                                                (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                                               (=>
                                                                  (not tobool8$2_0)
                                                                  (let
                                                                     ((result$2 dst$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              cmp2$1_0
                              (let
                                 ((tobool$1_0 (distinct length$1_0 0)))
                                 (=>
                                    (not tobool$1_0)
                                    (let
                                       ((result$1 dst0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             (not cmp$2_0)
                                             (let
                                                ((result$2 dst$2_0)
                                                 (HEAP$2_res HEAP$2))
                                                (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              (not cmp2$1_0)
                              (let
                                 ((add.ptr$1_0 (+ src0$1_0 length$1_0))
                                  (add.ptr8$1_0 (+ dst0$1_0 length$1_0))
                                  (tobool9$1_0 (distinct length$1_0 0)))
                                 (=>
                                    (not tobool9$1_0)
                                    (let
                                       ((result$1 dst0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   cmp1$2_0
                                                   (let
                                                      ((count.addr.0$2_0 count$2_0))
                                                      (let
                                                         ((a.0$2_0 dst$2_0)
                                                          (b.0$2_0 src$2_0)
                                                          (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                                          (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                                         (=>
                                                            (not tobool$2_0)
                                                            (let
                                                               ((result$2 dst$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              (not cmp2$1_0)
                              (let
                                 ((add.ptr$1_0 (+ src0$1_0 length$1_0))
                                  (add.ptr8$1_0 (+ dst0$1_0 length$1_0))
                                  (tobool9$1_0 (distinct length$1_0 0)))
                                 (=>
                                    (not tobool9$1_0)
                                    (let
                                       ((result$1 dst0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   (not cmp1$2_0)
                                                   (let
                                                      ((sub$2_0 (- count$2_0 1)))
                                                      (let
                                                         ((add.ptr$2_0 (+ dst$2_0 sub$2_0))
                                                          (sub4$2_0 (- count$2_0 1)))
                                                         (let
                                                            ((add.ptr5$2_0 (+ src$2_0 sub4$2_0))
                                                             (count.addr.1$2_0 count$2_0))
                                                            (let
                                                               ((a.1$2_0 add.ptr$2_0)
                                                                (b.1$2_0 add.ptr5$2_0)
                                                                (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                                                (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                                               (=>
                                                                  (not tobool8$2_0)
                                                                  (let
                                                                     ((result$2 dst$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              (not cmp2$1_0)
                              (let
                                 ((add.ptr$1_0 (+ src0$1_0 length$1_0))
                                  (add.ptr8$1_0 (+ dst0$1_0 length$1_0))
                                  (tobool9$1_0 (distinct length$1_0 0)))
                                 (=>
                                    (not tobool9$1_0)
                                    (let
                                       ((result$1 dst0$1_0)
                                        (HEAP$1_res HEAP$1)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             (not cmp$2_0)
                                             (let
                                                ((result$2 dst$2_0)
                                                 (HEAP$2_res HEAP$2))
                                                (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              cmp2$1_0
                              (let
                                 ((tobool$1_0 (distinct length$1_0 0)))
                                 (=>
                                    tobool$1_0
                                    (let
                                       ((dst.0$1_0 dst0$1_0)
                                        (src.0$1_0 src0$1_0)
                                        (t.0$1_0 length$1_0)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   cmp1$2_0
                                                   (let
                                                      ((count.addr.0$2_0 count$2_0))
                                                      (let
                                                         ((a.0$2_0 dst$2_0)
                                                          (b.0$2_0 src$2_0)
                                                          (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                                          (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                                         (=>
                                                            tobool$2_0
                                                            (INV_MAIN_0 dst.0$1_0 dst0$1_0 src.0$1_0 t.0$1_0 HEAP$1 a.0$2_0 b.0$2_0 dec$2_0 dst$2_0 HEAP$2)))))))))))))))))))))
(assert
   (forall
      ((dst0$1_0_old Int)
       (src0$1_0_old Int)
       (length$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (dst$2_0_old Int)
       (src$2_0_old Int)
       (count$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV dst0$1_0_old src0$1_0_old length$1_0_old HEAP$1_old dst$2_0_old src$2_0_old count$2_0_old HEAP$2_old)
         (let
            ((dst0$1_0 dst0$1_0_old)
             (src0$1_0 src0$1_0_old)
             (length$1_0 length$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (= length$1_0 0))
                (cmp1$1_0 (= dst0$1_0 src0$1_0)))
               (let
                  ((or.cond$1_0 (or
                                    cmp$1_0
                                    cmp1$1_0)))
                  (=>
                     (not or.cond$1_0)
                     (let
                        ((_$1_0 dst0$1_0)
                         (_$1_1 src0$1_0))
                        (let
                           ((cmp2$1_0 (< (abs _$1_0) (abs _$1_1))))
                           (=>
                              (not cmp2$1_0)
                              (let
                                 ((add.ptr$1_0 (+ src0$1_0 length$1_0))
                                  (add.ptr8$1_0 (+ dst0$1_0 length$1_0))
                                  (tobool9$1_0 (distinct length$1_0 0)))
                                 (=>
                                    tobool9$1_0
                                    (let
                                       ((dst.1$1_0 add.ptr8$1_0)
                                        (src.1$1_0 add.ptr$1_0)
                                        (t.1$1_0 length$1_0)
                                        (dst$2_0 dst$2_0_old)
                                        (src$2_0 src$2_0_old))
                                       (let
                                          ((count$2_0 count$2_0_old)
                                           (HEAP$2 HEAP$2_old)
                                           (cmp$2_0 (distinct src$2_0 dst$2_0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((cmp1$2_0 (> (abs src$2_0) (abs dst$2_0))))
                                                (=>
                                                   (not cmp1$2_0)
                                                   (let
                                                      ((sub$2_0 (- count$2_0 1)))
                                                      (let
                                                         ((add.ptr$2_0 (+ dst$2_0 sub$2_0))
                                                          (sub4$2_0 (- count$2_0 1)))
                                                         (let
                                                            ((add.ptr5$2_0 (+ src$2_0 sub4$2_0))
                                                             (count.addr.1$2_0 count$2_0))
                                                            (let
                                                               ((a.1$2_0 add.ptr$2_0)
                                                                (b.1$2_0 add.ptr5$2_0)
                                                                (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                                                (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                                               (=>
                                                                  tobool8$2_0
                                                                  (INV_MAIN_1 dst.1$1_0 dst0$1_0 src.1$1_0 t.1$1_0 HEAP$1 a.1$2_0 b.1$2_0 dec7$2_0 dst$2_0 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((dst.0$1_0_old Int)
       (dst0$1_0_old Int)
       (src.0$1_0_old Int)
       (t.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (b.0$2_0_old Int)
       (dec$2_0_old Int)
       (dst$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 dst.0$1_0_old dst0$1_0_old src.0$1_0_old t.0$1_0_old HEAP$1_old a.0$2_0_old b.0$2_0_old dec$2_0_old dst$2_0_old HEAP$2_old)
         (let
            ((dst.0$1_0 dst.0$1_0_old)
             (dst0$1_0 dst0$1_0_old)
             (src.0$1_0 src.0$1_0_old)
             (t.0$1_0 t.0$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((incdec.ptr$1_0 (+ src.0$1_0 1))
                (_$1_2 (select HEAP$1 src.0$1_0)))
               (let
                  ((incdec.ptr5$1_0 (+ dst.0$1_0 1))
                   (HEAP$1 (store HEAP$1 dst.0$1_0 _$1_2))
                   (dec$1_0 (+ t.0$1_0 (- 1))))
                  (let
                     ((tobool6$1_0 (distinct dec$1_0 0)))
                     (=>
                        (not tobool6$1_0)
                        (let
                           ((result$1 dst0$1_0)
                            (HEAP$1_res HEAP$1)
                            (a.0$2_0 a.0$2_0_old)
                            (b.0$2_0 b.0$2_0_old)
                            (dec$2_0 dec$2_0_old)
                            (dst$2_0 dst$2_0_old)
                            (HEAP$2 HEAP$2_old))
                           (let
                              ((incdec.ptr$2_0 (+ b.0$2_0 1))
                               (_$2_0 (select HEAP$2 b.0$2_0)))
                              (let
                                 ((incdec.ptr3$2_0 (+ a.0$2_0 1))
                                  (HEAP$2 (store HEAP$2 a.0$2_0 _$2_0))
                                  (count.addr.0$2_0 dec$2_0))
                                 (let
                                    ((a.0$2_0 incdec.ptr3$2_0)
                                     (b.0$2_0 incdec.ptr$2_0)
                                     (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                     (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                    (=>
                                       (not tobool$2_0)
                                       (let
                                          ((result$2 dst$2_0)
                                           (HEAP$2_res HEAP$2))
                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))
(assert
   (forall
      ((dst.0$1_0_old Int)
       (dst0$1_0_old Int)
       (src.0$1_0_old Int)
       (t.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (b.0$2_0_old Int)
       (dec$2_0_old Int)
       (dst$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 dst.0$1_0_old dst0$1_0_old src.0$1_0_old t.0$1_0_old HEAP$1_old a.0$2_0_old b.0$2_0_old dec$2_0_old dst$2_0_old HEAP$2_old)
         (let
            ((dst.0$1_0 dst.0$1_0_old)
             (dst0$1_0 dst0$1_0_old)
             (src.0$1_0 src.0$1_0_old)
             (t.0$1_0 t.0$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((incdec.ptr$1_0 (+ src.0$1_0 1))
                (_$1_2 (select HEAP$1 src.0$1_0)))
               (let
                  ((incdec.ptr5$1_0 (+ dst.0$1_0 1))
                   (HEAP$1 (store HEAP$1 dst.0$1_0 _$1_2))
                   (dec$1_0 (+ t.0$1_0 (- 1))))
                  (let
                     ((tobool6$1_0 (distinct dec$1_0 0)))
                     (=>
                        tobool6$1_0
                        (let
                           ((dst.0$1_0 incdec.ptr5$1_0)
                            (src.0$1_0 incdec.ptr$1_0)
                            (t.0$1_0 dec$1_0)
                            (a.0$2_0 a.0$2_0_old)
                            (b.0$2_0 b.0$2_0_old)
                            (dec$2_0 dec$2_0_old)
                            (dst$2_0 dst$2_0_old)
                            (HEAP$2 HEAP$2_old))
                           (let
                              ((incdec.ptr$2_0 (+ b.0$2_0 1))
                               (_$2_0 (select HEAP$2 b.0$2_0)))
                              (let
                                 ((incdec.ptr3$2_0 (+ a.0$2_0 1))
                                  (HEAP$2 (store HEAP$2 a.0$2_0 _$2_0))
                                  (count.addr.0$2_0 dec$2_0))
                                 (let
                                    ((a.0$2_0 incdec.ptr3$2_0)
                                     (b.0$2_0 incdec.ptr$2_0)
                                     (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                     (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                    (=>
                                       tobool$2_0
                                       (INV_MAIN_0 dst.0$1_0 dst0$1_0 src.0$1_0 t.0$1_0 HEAP$1 a.0$2_0 b.0$2_0 dec$2_0 dst$2_0 HEAP$2))))))))))))))
(assert
   (forall
      ((dst.0$1_0_old Int)
       (dst0$1_0_old Int)
       (src.0$1_0_old Int)
       (t.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (b.0$2_0_old Int)
       (dec$2_0_old Int)
       (dst$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 dst.0$1_0_old dst0$1_0_old src.0$1_0_old t.0$1_0_old HEAP$1_old a.0$2_0_old b.0$2_0_old dec$2_0_old dst$2_0_old HEAP$2_old)
         (let
            ((dst.0$1_0 dst.0$1_0_old)
             (dst0$1_0 dst0$1_0_old)
             (src.0$1_0 src.0$1_0_old)
             (t.0$1_0 t.0$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((incdec.ptr$1_0 (+ src.0$1_0 1))
                (_$1_2 (select HEAP$1 src.0$1_0)))
               (let
                  ((incdec.ptr5$1_0 (+ dst.0$1_0 1))
                   (HEAP$1 (store HEAP$1 dst.0$1_0 _$1_2))
                   (dec$1_0 (+ t.0$1_0 (- 1))))
                  (let
                     ((tobool6$1_0 (distinct dec$1_0 0)))
                     (=>
                        tobool6$1_0
                        (let
                           ((dst.0$1_0 incdec.ptr5$1_0)
                            (src.0$1_0 incdec.ptr$1_0)
                            (t.0$1_0 dec$1_0))
                           (=>
                              (let
                                 ((a.0$2_0 a.0$2_0_old)
                                  (b.0$2_0 b.0$2_0_old)
                                  (dec$2_0 dec$2_0_old)
                                  (dst$2_0 dst$2_0_old)
                                  (HEAP$2 HEAP$2_old))
                                 (let
                                    ((incdec.ptr$2_0 (+ b.0$2_0 1))
                                     (_$2_0 (select HEAP$2 b.0$2_0)))
                                    (let
                                       ((incdec.ptr3$2_0 (+ a.0$2_0 1))
                                        (HEAP$2 (store HEAP$2 a.0$2_0 _$2_0))
                                        (count.addr.0$2_0 dec$2_0))
                                       (let
                                          ((a.0$2_0 incdec.ptr3$2_0)
                                           (b.0$2_0 incdec.ptr$2_0)
                                           (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                                           (tobool$2_0 (distinct count.addr.0$2_0 0)))
                                          (not tobool$2_0)))))
                              (INV_MAIN_0 dst.0$1_0 dst0$1_0 src.0$1_0 t.0$1_0 HEAP$1 a.0$2_0_old b.0$2_0_old dec$2_0_old dst$2_0_old HEAP$2_old)))))))))))
(assert
   (forall
      ((dst.0$1_0_old Int)
       (dst0$1_0_old Int)
       (src.0$1_0_old Int)
       (t.0$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.0$2_0_old Int)
       (b.0$2_0_old Int)
       (dec$2_0_old Int)
       (dst$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_0 dst.0$1_0_old dst0$1_0_old src.0$1_0_old t.0$1_0_old HEAP$1_old a.0$2_0_old b.0$2_0_old dec$2_0_old dst$2_0_old HEAP$2_old)
         (let
            ((a.0$2_0 a.0$2_0_old)
             (b.0$2_0 b.0$2_0_old)
             (dec$2_0 dec$2_0_old)
             (dst$2_0 dst$2_0_old)
             (HEAP$2 HEAP$2_old))
            (let
               ((incdec.ptr$2_0 (+ b.0$2_0 1))
                (_$2_0 (select HEAP$2 b.0$2_0)))
               (let
                  ((incdec.ptr3$2_0 (+ a.0$2_0 1))
                   (HEAP$2 (store HEAP$2 a.0$2_0 _$2_0))
                   (count.addr.0$2_0 dec$2_0))
                  (let
                     ((a.0$2_0 incdec.ptr3$2_0)
                      (b.0$2_0 incdec.ptr$2_0)
                      (dec$2_0 (+ count.addr.0$2_0 (- 1)))
                      (tobool$2_0 (distinct count.addr.0$2_0 0)))
                     (=>
                        tobool$2_0
                        (=>
                           (let
                              ((dst.0$1_0 dst.0$1_0_old)
                               (dst0$1_0 dst0$1_0_old)
                               (src.0$1_0 src.0$1_0_old)
                               (t.0$1_0 t.0$1_0_old)
                               (HEAP$1 HEAP$1_old))
                              (let
                                 ((incdec.ptr$1_0 (+ src.0$1_0 1))
                                  (_$1_2 (select HEAP$1 src.0$1_0)))
                                 (let
                                    ((incdec.ptr5$1_0 (+ dst.0$1_0 1))
                                     (HEAP$1 (store HEAP$1 dst.0$1_0 _$1_2))
                                     (dec$1_0 (+ t.0$1_0 (- 1))))
                                    (let
                                       ((tobool6$1_0 (distinct dec$1_0 0)))
                                       (=>
                                          tobool6$1_0
                                          (let
                                             ((dst.0$1_0 incdec.ptr5$1_0)
                                              (src.0$1_0 incdec.ptr$1_0)
                                              (t.0$1_0 dec$1_0))
                                             false))))))
                           (INV_MAIN_0 dst.0$1_0_old dst0$1_0_old src.0$1_0_old t.0$1_0_old HEAP$1_old a.0$2_0 b.0$2_0 dec$2_0 dst$2_0 HEAP$2))))))))))
(assert
   (forall
      ((dst.1$1_0_old Int)
       (dst0$1_0_old Int)
       (src.1$1_0_old Int)
       (t.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.1$2_0_old Int)
       (b.1$2_0_old Int)
       (dec7$2_0_old Int)
       (dst$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 dst.1$1_0_old dst0$1_0_old src.1$1_0_old t.1$1_0_old HEAP$1_old a.1$2_0_old b.1$2_0_old dec7$2_0_old dst$2_0_old HEAP$2_old)
         (let
            ((dst.1$1_0 dst.1$1_0_old)
             (dst0$1_0 dst0$1_0_old)
             (src.1$1_0 src.1$1_0_old))
            (let
               ((t.1$1_0 t.1$1_0_old)
                (HEAP$1 HEAP$1_old)
                (incdec.ptr12$1_0 (+ src.1$1_0 (- 1))))
               (let
                  ((_$1_3 (select HEAP$1 incdec.ptr12$1_0))
                   (incdec.ptr13$1_0 (+ dst.1$1_0 (- 1))))
                  (let
                     ((HEAP$1 (store HEAP$1 incdec.ptr13$1_0 _$1_3))
                      (dec17$1_0 (+ t.1$1_0 (- 1))))
                     (let
                        ((tobool19$1_0 (distinct dec17$1_0 0)))
                        (=>
                           (not tobool19$1_0)
                           (let
                              ((result$1 dst0$1_0)
                               (HEAP$1_res HEAP$1)
                               (a.1$2_0 a.1$2_0_old)
                               (b.1$2_0 b.1$2_0_old)
                               (dec7$2_0 dec7$2_0_old)
                               (dst$2_0 dst$2_0_old)
                               (HEAP$2 HEAP$2_old))
                              (let
                                 ((incdec.ptr10$2_0 (+ b.1$2_0 (- 1)))
                                  (_$2_1 (select HEAP$2 b.1$2_0)))
                                 (let
                                    ((incdec.ptr11$2_0 (+ a.1$2_0 (- 1)))
                                     (HEAP$2 (store HEAP$2 a.1$2_0 _$2_1))
                                     (count.addr.1$2_0 dec7$2_0))
                                    (let
                                       ((a.1$2_0 incdec.ptr11$2_0)
                                        (b.1$2_0 incdec.ptr10$2_0)
                                        (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                        (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                       (=>
                                          (not tobool8$2_0)
                                          (let
                                             ((result$2 dst$2_0)
                                              (HEAP$2_res HEAP$2))
                                             (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))
(assert
   (forall
      ((dst.1$1_0_old Int)
       (dst0$1_0_old Int)
       (src.1$1_0_old Int)
       (t.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.1$2_0_old Int)
       (b.1$2_0_old Int)
       (dec7$2_0_old Int)
       (dst$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 dst.1$1_0_old dst0$1_0_old src.1$1_0_old t.1$1_0_old HEAP$1_old a.1$2_0_old b.1$2_0_old dec7$2_0_old dst$2_0_old HEAP$2_old)
         (let
            ((dst.1$1_0 dst.1$1_0_old)
             (dst0$1_0 dst0$1_0_old)
             (src.1$1_0 src.1$1_0_old))
            (let
               ((t.1$1_0 t.1$1_0_old)
                (HEAP$1 HEAP$1_old)
                (incdec.ptr12$1_0 (+ src.1$1_0 (- 1))))
               (let
                  ((_$1_3 (select HEAP$1 incdec.ptr12$1_0))
                   (incdec.ptr13$1_0 (+ dst.1$1_0 (- 1))))
                  (let
                     ((HEAP$1 (store HEAP$1 incdec.ptr13$1_0 _$1_3))
                      (dec17$1_0 (+ t.1$1_0 (- 1))))
                     (let
                        ((tobool19$1_0 (distinct dec17$1_0 0)))
                        (=>
                           tobool19$1_0
                           (let
                              ((dst.1$1_0 incdec.ptr13$1_0)
                               (src.1$1_0 incdec.ptr12$1_0)
                               (t.1$1_0 dec17$1_0)
                               (a.1$2_0 a.1$2_0_old)
                               (b.1$2_0 b.1$2_0_old)
                               (dec7$2_0 dec7$2_0_old)
                               (dst$2_0 dst$2_0_old)
                               (HEAP$2 HEAP$2_old))
                              (let
                                 ((incdec.ptr10$2_0 (+ b.1$2_0 (- 1)))
                                  (_$2_1 (select HEAP$2 b.1$2_0)))
                                 (let
                                    ((incdec.ptr11$2_0 (+ a.1$2_0 (- 1)))
                                     (HEAP$2 (store HEAP$2 a.1$2_0 _$2_1))
                                     (count.addr.1$2_0 dec7$2_0))
                                    (let
                                       ((a.1$2_0 incdec.ptr11$2_0)
                                        (b.1$2_0 incdec.ptr10$2_0)
                                        (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                        (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                       (=>
                                          tobool8$2_0
                                          (INV_MAIN_1 dst.1$1_0 dst0$1_0 src.1$1_0 t.1$1_0 HEAP$1 a.1$2_0 b.1$2_0 dec7$2_0 dst$2_0 HEAP$2)))))))))))))))
(assert
   (forall
      ((dst.1$1_0_old Int)
       (dst0$1_0_old Int)
       (src.1$1_0_old Int)
       (t.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.1$2_0_old Int)
       (b.1$2_0_old Int)
       (dec7$2_0_old Int)
       (dst$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 dst.1$1_0_old dst0$1_0_old src.1$1_0_old t.1$1_0_old HEAP$1_old a.1$2_0_old b.1$2_0_old dec7$2_0_old dst$2_0_old HEAP$2_old)
         (let
            ((dst.1$1_0 dst.1$1_0_old)
             (dst0$1_0 dst0$1_0_old)
             (src.1$1_0 src.1$1_0_old))
            (let
               ((t.1$1_0 t.1$1_0_old)
                (HEAP$1 HEAP$1_old)
                (incdec.ptr12$1_0 (+ src.1$1_0 (- 1))))
               (let
                  ((_$1_3 (select HEAP$1 incdec.ptr12$1_0))
                   (incdec.ptr13$1_0 (+ dst.1$1_0 (- 1))))
                  (let
                     ((HEAP$1 (store HEAP$1 incdec.ptr13$1_0 _$1_3))
                      (dec17$1_0 (+ t.1$1_0 (- 1))))
                     (let
                        ((tobool19$1_0 (distinct dec17$1_0 0)))
                        (=>
                           tobool19$1_0
                           (let
                              ((dst.1$1_0 incdec.ptr13$1_0)
                               (src.1$1_0 incdec.ptr12$1_0)
                               (t.1$1_0 dec17$1_0))
                              (=>
                                 (let
                                    ((a.1$2_0 a.1$2_0_old)
                                     (b.1$2_0 b.1$2_0_old)
                                     (dec7$2_0 dec7$2_0_old)
                                     (dst$2_0 dst$2_0_old)
                                     (HEAP$2 HEAP$2_old))
                                    (let
                                       ((incdec.ptr10$2_0 (+ b.1$2_0 (- 1)))
                                        (_$2_1 (select HEAP$2 b.1$2_0)))
                                       (let
                                          ((incdec.ptr11$2_0 (+ a.1$2_0 (- 1)))
                                           (HEAP$2 (store HEAP$2 a.1$2_0 _$2_1))
                                           (count.addr.1$2_0 dec7$2_0))
                                          (let
                                             ((a.1$2_0 incdec.ptr11$2_0)
                                              (b.1$2_0 incdec.ptr10$2_0)
                                              (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                                              (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                                             (not tobool8$2_0)))))
                                 (INV_MAIN_1 dst.1$1_0 dst0$1_0 src.1$1_0 t.1$1_0 HEAP$1 a.1$2_0_old b.1$2_0_old dec7$2_0_old dst$2_0_old HEAP$2_old))))))))))))
(assert
   (forall
      ((dst.1$1_0_old Int)
       (dst0$1_0_old Int)
       (src.1$1_0_old Int)
       (t.1$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a.1$2_0_old Int)
       (b.1$2_0_old Int)
       (dec7$2_0_old Int)
       (dst$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_1 dst.1$1_0_old dst0$1_0_old src.1$1_0_old t.1$1_0_old HEAP$1_old a.1$2_0_old b.1$2_0_old dec7$2_0_old dst$2_0_old HEAP$2_old)
         (let
            ((a.1$2_0 a.1$2_0_old)
             (b.1$2_0 b.1$2_0_old)
             (dec7$2_0 dec7$2_0_old)
             (dst$2_0 dst$2_0_old)
             (HEAP$2 HEAP$2_old))
            (let
               ((incdec.ptr10$2_0 (+ b.1$2_0 (- 1)))
                (_$2_1 (select HEAP$2 b.1$2_0)))
               (let
                  ((incdec.ptr11$2_0 (+ a.1$2_0 (- 1)))
                   (HEAP$2 (store HEAP$2 a.1$2_0 _$2_1))
                   (count.addr.1$2_0 dec7$2_0))
                  (let
                     ((a.1$2_0 incdec.ptr11$2_0)
                      (b.1$2_0 incdec.ptr10$2_0)
                      (dec7$2_0 (+ count.addr.1$2_0 (- 1)))
                      (tobool8$2_0 (distinct count.addr.1$2_0 0)))
                     (=>
                        tobool8$2_0
                        (=>
                           (let
                              ((dst.1$1_0 dst.1$1_0_old)
                               (dst0$1_0 dst0$1_0_old)
                               (src.1$1_0 src.1$1_0_old))
                              (let
                                 ((t.1$1_0 t.1$1_0_old)
                                  (HEAP$1 HEAP$1_old)
                                  (incdec.ptr12$1_0 (+ src.1$1_0 (- 1))))
                                 (let
                                    ((_$1_3 (select HEAP$1 incdec.ptr12$1_0))
                                     (incdec.ptr13$1_0 (+ dst.1$1_0 (- 1))))
                                    (let
                                       ((HEAP$1 (store HEAP$1 incdec.ptr13$1_0 _$1_3))
                                        (dec17$1_0 (+ t.1$1_0 (- 1))))
                                       (let
                                          ((tobool19$1_0 (distinct dec17$1_0 0)))
                                          (=>
                                             tobool19$1_0
                                             (let
                                                ((dst.1$1_0 incdec.ptr13$1_0)
                                                 (src.1$1_0 incdec.ptr12$1_0)
                                                 (t.1$1_0 dec17$1_0))
                                                false)))))))
                           (INV_MAIN_1 dst.1$1_0_old dst0$1_0_old src.1$1_0_old t.1$1_0_old HEAP$1_old a.1$2_0 b.1$2_0 dec7$2_0 dst$2_0 HEAP$2))))))))))
(check-sat)
(get-model)
