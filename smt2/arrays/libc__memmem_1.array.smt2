;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   INV_REC_memcmp^memcmp
   ((_$1_0 Int)
    (_$1_1 Int)
    (_$1_2 Int)
    (HEAP$1 (Array Int Int))
    (_$2_0 Int)
    (_$2_1 Int)
    (_$2_2 Int)
    (HEAP$2 (Array Int Int))
    (result$1 Int)
    (result$2 Int)
    (HEAP$1_res (Array Int Int))
    (HEAP$2_res (Array Int Int)))
   Bool
   (=>
      (and
         (= _$1_0 _$2_0)
         (= _$1_1 _$2_1)
         (= _$1_2 _$2_2)
         (= HEAP$1 HEAP$2))
      (and
         (= result$1 result$2)
         (= HEAP$1_res HEAP$2_res))))
(define-fun
   INV_REC_memcmp__1
   ((_$1_0 Int)
    (_$1_1 Int)
    (_$1_2 Int)
    (HEAP (Array Int Int))
    (result$1 Int)
    (HEAP$1_res (Array Int Int)))
   Bool
   true)
(define-fun
   INV_REC_memcmp__2
   ((_$2_0 Int)
    (_$2_1 Int)
    (_$2_2 Int)
    (HEAP (Array Int Int))
    (result$2 Int)
    (HEAP$2_res (Array Int Int)))
   Bool
   true)
(define-fun
   IN_INV
   ((haystack$1_0 Int)
    (hl$1_0 Int)
    (needle$1_0 Int)
    (nl$1_0 Int)
    (HEAP$1 (Array Int Int))
    (haystack$2_0 Int)
    (hl$2_0 Int)
    (needle$2_0 Int)
    (nl$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= haystack$1_0 haystack$2_0)
      (= hl$1_0 hl$2_0)
      (= needle$1_0 needle$2_0)
      (= nl$1_0 nl$2_0)
      (>= haystack$1_0 0)
      (>= hl$1_0 0)
      (>= nl$1_0 0)
      (>= needle$1_0 0)
      (forall
         ((i_0 Int))
         (= (select HEAP$1 i_0) (select HEAP$2 i_0)))))
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
; :annot (INV_MAIN_42 add.ptr1$1_0 cur.0$1_0 needle$1_0 nl$1_0 HEAP$1 haystack.addr.0$2_0 i.0$2_0 needle$2_0 nl$2_0 HEAP$2)
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
      ((haystack$1_0_old Int)
       (hl$1_0_old Int)
       (needle$1_0_old Int)
       (nl$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (haystack$2_0_old Int)
       (hl$2_0_old Int)
       (needle$2_0_old Int)
       (nl$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV haystack$1_0_old hl$1_0_old needle$1_0_old nl$1_0_old HEAP$1_old haystack$2_0_old hl$2_0_old needle$2_0_old nl$2_0_old HEAP$2_old)
         (let
            ((haystack$1_0 haystack$1_0_old)
             (hl$1_0 hl$1_0_old)
             (needle$1_0 needle$1_0_old)
             (nl$1_0 nl$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (< (abs hl$1_0) (abs nl$1_0))))
               (=>
                  cmp$1_0
                  (let
                     ((retval.0$1_0 0))
                     (let
                        ((result$1 retval.0$1_0)
                         (HEAP$1_res HEAP$1)
                         (haystack$2_0 haystack$2_0_old)
                         (hl$2_0 hl$2_0_old)
                         (needle$2_0 needle$2_0_old)
                         (nl$2_0 nl$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (cmp$2_0 (> (abs nl$2_0) (abs hl$2_0))))
                           (=>
                              (not cmp$2_0)
                              (let
                                 ((sub$2_0 (- hl$2_0 nl$2_0)))
                                 (let
                                    ((add$2_0 (+ sub$2_0 1)))
                                    (let
                                       ((conv$2_0 add$2_0))
                                       (let
                                          ((i.0$2_0 conv$2_0)
                                           (haystack.addr.0$2_0 haystack$2_0))
                                          false))))))))))))))
(assert
   (forall
      ((haystack$1_0_old Int)
       (hl$1_0_old Int)
       (needle$1_0_old Int)
       (nl$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (haystack$2_0_old Int)
       (hl$2_0_old Int)
       (needle$2_0_old Int)
       (nl$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV haystack$1_0_old hl$1_0_old needle$1_0_old nl$1_0_old HEAP$1_old haystack$2_0_old hl$2_0_old needle$2_0_old nl$2_0_old HEAP$2_old)
         (let
            ((haystack$1_0 haystack$1_0_old)
             (hl$1_0 hl$1_0_old)
             (needle$1_0 needle$1_0_old)
             (nl$1_0 nl$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (< (abs hl$1_0) (abs nl$1_0))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((add.ptr$1_0 (+ haystack$1_0 hl$1_0))
                      (idx.neg$1_0 (- 0 nl$1_0)))
                     (let
                        ((add.ptr1$1_0 (+ add.ptr$1_0 idx.neg$1_0))
                         (cur.0$1_0 haystack$1_0)
                         (haystack$2_0 haystack$2_0_old)
                         (hl$2_0 hl$2_0_old)
                         (needle$2_0 needle$2_0_old)
                         (nl$2_0 nl$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (cmp$2_0 (> (abs nl$2_0) (abs hl$2_0))))
                           (=>
                              cmp$2_0
                              (let
                                 ((retval.0$2_0 0))
                                 (let
                                    ((result$2 retval.0$2_0)
                                     (HEAP$2_res HEAP$2))
                                    false))))))))))))
(assert
   (forall
      ((haystack$1_0_old Int)
       (hl$1_0_old Int)
       (needle$1_0_old Int)
       (nl$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (haystack$2_0_old Int)
       (hl$2_0_old Int)
       (needle$2_0_old Int)
       (nl$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV haystack$1_0_old hl$1_0_old needle$1_0_old nl$1_0_old HEAP$1_old haystack$2_0_old hl$2_0_old needle$2_0_old nl$2_0_old HEAP$2_old)
         (let
            ((haystack$1_0 haystack$1_0_old)
             (hl$1_0 hl$1_0_old)
             (needle$1_0 needle$1_0_old)
             (nl$1_0 nl$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (< (abs hl$1_0) (abs nl$1_0))))
               (=>
                  cmp$1_0
                  (let
                     ((retval.0$1_0 0))
                     (let
                        ((result$1 retval.0$1_0)
                         (HEAP$1_res HEAP$1)
                         (haystack$2_0 haystack$2_0_old)
                         (hl$2_0 hl$2_0_old)
                         (needle$2_0 needle$2_0_old)
                         (nl$2_0 nl$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (cmp$2_0 (> (abs nl$2_0) (abs hl$2_0))))
                           (=>
                              cmp$2_0
                              (let
                                 ((retval.0$2_0 0))
                                 (let
                                    ((result$2 retval.0$2_0)
                                     (HEAP$2_res HEAP$2))
                                    (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))
(assert
   (forall
      ((haystack$1_0_old Int)
       (hl$1_0_old Int)
       (needle$1_0_old Int)
       (nl$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (haystack$2_0_old Int)
       (hl$2_0_old Int)
       (needle$2_0_old Int)
       (nl$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV haystack$1_0_old hl$1_0_old needle$1_0_old nl$1_0_old HEAP$1_old haystack$2_0_old hl$2_0_old needle$2_0_old nl$2_0_old HEAP$2_old)
         (let
            ((haystack$1_0 haystack$1_0_old)
             (hl$1_0 hl$1_0_old)
             (needle$1_0 needle$1_0_old)
             (nl$1_0 nl$1_0_old))
            (let
               ((HEAP$1 HEAP$1_old)
                (cmp$1_0 (< (abs hl$1_0) (abs nl$1_0))))
               (=>
                  (not cmp$1_0)
                  (let
                     ((add.ptr$1_0 (+ haystack$1_0 hl$1_0))
                      (idx.neg$1_0 (- 0 nl$1_0)))
                     (let
                        ((add.ptr1$1_0 (+ add.ptr$1_0 idx.neg$1_0))
                         (cur.0$1_0 haystack$1_0)
                         (haystack$2_0 haystack$2_0_old)
                         (hl$2_0 hl$2_0_old)
                         (needle$2_0 needle$2_0_old)
                         (nl$2_0 nl$2_0_old))
                        (let
                           ((HEAP$2 HEAP$2_old)
                            (cmp$2_0 (> (abs nl$2_0) (abs hl$2_0))))
                           (=>
                              (not cmp$2_0)
                              (let
                                 ((sub$2_0 (- hl$2_0 nl$2_0)))
                                 (let
                                    ((add$2_0 (+ sub$2_0 1)))
                                    (let
                                       ((conv$2_0 add$2_0))
                                       (let
                                          ((i.0$2_0 conv$2_0)
                                           (haystack.addr.0$2_0 haystack$2_0))
                                          (INV_MAIN_42 add.ptr1$1_0 cur.0$1_0 needle$1_0 nl$1_0 HEAP$1 haystack.addr.0$2_0 i.0$2_0 needle$2_0 nl$2_0 HEAP$2)))))))))))))))
(assert
   (forall
      ((add.ptr1$1_0_old Int)
       (cur.0$1_0_old Int)
       (needle$1_0_old Int)
       (nl$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (haystack.addr.0$2_0_old Int)
       (i.0$2_0_old Int)
       (needle$2_0_old Int)
       (nl$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 add.ptr1$1_0_old cur.0$1_0_old needle$1_0_old nl$1_0_old HEAP$1_old haystack.addr.0$2_0_old i.0$2_0_old needle$2_0_old nl$2_0_old HEAP$2_old)
         (let
            ((add.ptr1$1_0 add.ptr1$1_0_old)
             (cur.0$1_0 cur.0$1_0_old))
            (let
               ((needle$1_0 needle$1_0_old)
                (nl$1_0 nl$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp2$1_0 (<= (abs cur.0$1_0) (abs add.ptr1$1_0))))
               (=>
                  cmp2$1_0
                  (let
                     ((HEAP$1 HEAP$1)
                      (haystack.addr.0$2_0 haystack.addr.0$2_0_old)
                      (i.0$2_0 i.0$2_0_old))
                     (let
                        ((needle$2_0 needle$2_0_old)
                         (nl$2_0 nl$2_0_old)
                         (HEAP$2 HEAP$2_old)
                         (tobool$2_0 (distinct i.0$2_0 0)))
                        (=>
                           tobool$2_0
                           (let
                              ((HEAP$2 HEAP$2))
                              (forall
                                 ((call3$1_0 Int)
                                  (call1$2_0 Int)
                                  (HEAP$1_res (Array Int Int))
                                  (HEAP$2_res (Array Int Int)))
                                 (=>
                                    (INV_REC_memcmp^memcmp cur.0$1_0 needle$1_0 nl$1_0 HEAP$1 haystack.addr.0$2_0 needle$2_0 nl$2_0 HEAP$2 call3$1_0 call1$2_0 HEAP$1_res HEAP$2_res)
                                    (let
                                       ((HEAP$1 HEAP$1_res)
                                        (cmp4$1_0 (= call3$1_0 0)))
                                       (=>
                                          cmp4$1_0
                                          (let
                                             ((retval.0$1_0 cur.0$1_0))
                                             (let
                                                ((result$1 retval.0$1_0)
                                                 (HEAP$1_res HEAP$1)
                                                 (HEAP$2 HEAP$2_res)
                                                 (tobool2$2_0 (distinct call1$2_0 0)))
                                                (=>
                                                   (not tobool2$2_0)
                                                   (let
                                                      ((retval.0$2_0 haystack.addr.0$2_0))
                                                      (let
                                                         ((result$2 retval.0$2_0)
                                                          (HEAP$2_res HEAP$2))
                                                         (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))
(assert
   (forall
      ((add.ptr1$1_0_old Int)
       (cur.0$1_0_old Int)
       (needle$1_0_old Int)
       (nl$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (haystack.addr.0$2_0_old Int)
       (i.0$2_0_old Int)
       (needle$2_0_old Int)
       (nl$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 add.ptr1$1_0_old cur.0$1_0_old needle$1_0_old nl$1_0_old HEAP$1_old haystack.addr.0$2_0_old i.0$2_0_old needle$2_0_old nl$2_0_old HEAP$2_old)
         (let
            ((add.ptr1$1_0 add.ptr1$1_0_old)
             (cur.0$1_0 cur.0$1_0_old))
            (let
               ((needle$1_0 needle$1_0_old)
                (nl$1_0 nl$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp2$1_0 (<= (abs cur.0$1_0) (abs add.ptr1$1_0))))
               (=>
                  cmp2$1_0
                  (let
                     ((HEAP$1 HEAP$1)
                      (haystack.addr.0$2_0 haystack.addr.0$2_0_old)
                      (i.0$2_0 i.0$2_0_old))
                     (let
                        ((needle$2_0 needle$2_0_old)
                         (nl$2_0 nl$2_0_old)
                         (HEAP$2 HEAP$2_old)
                         (tobool$2_0 (distinct i.0$2_0 0)))
                        (=>
                           (not tobool$2_0)
                           (let
                              ((retval.0$2_0 0))
                              (let
                                 ((result$2 retval.0$2_0)
                                  (HEAP$2_res HEAP$2))
                                 (forall
                                    ((call3$1_0 Int)
                                     (HEAP$1_res (Array Int Int)))
                                    (=>
                                       (INV_REC_memcmp__1 cur.0$1_0 needle$1_0 nl$1_0 HEAP$1 call3$1_0 HEAP$1_res)
                                       (let
                                          ((HEAP$1 HEAP$1_res)
                                           (cmp4$1_0 (= call3$1_0 0)))
                                          (=>
                                             cmp4$1_0
                                             (let
                                                ((retval.0$1_0 cur.0$1_0))
                                                (let
                                                   ((result$1 retval.0$1_0)
                                                    (HEAP$1_res HEAP$1))
                                                   (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))
(assert
   (forall
      ((add.ptr1$1_0_old Int)
       (cur.0$1_0_old Int)
       (needle$1_0_old Int)
       (nl$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (haystack.addr.0$2_0_old Int)
       (i.0$2_0_old Int)
       (needle$2_0_old Int)
       (nl$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 add.ptr1$1_0_old cur.0$1_0_old needle$1_0_old nl$1_0_old HEAP$1_old haystack.addr.0$2_0_old i.0$2_0_old needle$2_0_old nl$2_0_old HEAP$2_old)
         (let
            ((add.ptr1$1_0 add.ptr1$1_0_old)
             (cur.0$1_0 cur.0$1_0_old))
            (let
               ((needle$1_0 needle$1_0_old)
                (nl$1_0 nl$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp2$1_0 (<= (abs cur.0$1_0) (abs add.ptr1$1_0))))
               (=>
                  (not cmp2$1_0)
                  (let
                     ((retval.0$1_0 0))
                     (let
                        ((result$1 retval.0$1_0)
                         (HEAP$1_res HEAP$1)
                         (haystack.addr.0$2_0 haystack.addr.0$2_0_old)
                         (i.0$2_0 i.0$2_0_old))
                        (let
                           ((needle$2_0 needle$2_0_old)
                            (nl$2_0 nl$2_0_old)
                            (HEAP$2 HEAP$2_old)
                            (tobool$2_0 (distinct i.0$2_0 0)))
                           (=>
                              tobool$2_0
                              (let
                                 ((HEAP$2 HEAP$2))
                                 (forall
                                    ((call1$2_0 Int)
                                     (HEAP$2_res (Array Int Int)))
                                    (=>
                                       (INV_REC_memcmp__2 haystack.addr.0$2_0 needle$2_0 nl$2_0 HEAP$2 call1$2_0 HEAP$2_res)
                                       (let
                                          ((HEAP$2 HEAP$2_res)
                                           (tobool2$2_0 (distinct call1$2_0 0)))
                                          (=>
                                             (not tobool2$2_0)
                                             (let
                                                ((retval.0$2_0 haystack.addr.0$2_0))
                                                (let
                                                   ((result$2 retval.0$2_0)
                                                    (HEAP$2_res HEAP$2))
                                                   (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))
(assert
   (forall
      ((add.ptr1$1_0_old Int)
       (cur.0$1_0_old Int)
       (needle$1_0_old Int)
       (nl$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (haystack.addr.0$2_0_old Int)
       (i.0$2_0_old Int)
       (needle$2_0_old Int)
       (nl$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 add.ptr1$1_0_old cur.0$1_0_old needle$1_0_old nl$1_0_old HEAP$1_old haystack.addr.0$2_0_old i.0$2_0_old needle$2_0_old nl$2_0_old HEAP$2_old)
         (let
            ((add.ptr1$1_0 add.ptr1$1_0_old)
             (cur.0$1_0 cur.0$1_0_old))
            (let
               ((needle$1_0 needle$1_0_old)
                (nl$1_0 nl$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp2$1_0 (<= (abs cur.0$1_0) (abs add.ptr1$1_0))))
               (=>
                  (not cmp2$1_0)
                  (let
                     ((retval.0$1_0 0))
                     (let
                        ((result$1 retval.0$1_0)
                         (HEAP$1_res HEAP$1)
                         (haystack.addr.0$2_0 haystack.addr.0$2_0_old)
                         (i.0$2_0 i.0$2_0_old))
                        (let
                           ((needle$2_0 needle$2_0_old)
                            (nl$2_0 nl$2_0_old)
                            (HEAP$2 HEAP$2_old)
                            (tobool$2_0 (distinct i.0$2_0 0)))
                           (=>
                              (not tobool$2_0)
                              (let
                                 ((retval.0$2_0 0))
                                 (let
                                    ((result$2 retval.0$2_0)
                                     (HEAP$2_res HEAP$2))
                                    (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))
(assert
   (forall
      ((add.ptr1$1_0_old Int)
       (cur.0$1_0_old Int)
       (needle$1_0_old Int)
       (nl$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (haystack.addr.0$2_0_old Int)
       (i.0$2_0_old Int)
       (needle$2_0_old Int)
       (nl$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 add.ptr1$1_0_old cur.0$1_0_old needle$1_0_old nl$1_0_old HEAP$1_old haystack.addr.0$2_0_old i.0$2_0_old needle$2_0_old nl$2_0_old HEAP$2_old)
         (let
            ((add.ptr1$1_0 add.ptr1$1_0_old)
             (cur.0$1_0 cur.0$1_0_old))
            (let
               ((needle$1_0 needle$1_0_old)
                (nl$1_0 nl$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp2$1_0 (<= (abs cur.0$1_0) (abs add.ptr1$1_0))))
               (=>
                  cmp2$1_0
                  (let
                     ((HEAP$1 HEAP$1)
                      (haystack.addr.0$2_0 haystack.addr.0$2_0_old)
                      (i.0$2_0 i.0$2_0_old))
                     (let
                        ((needle$2_0 needle$2_0_old)
                         (nl$2_0 nl$2_0_old)
                         (HEAP$2 HEAP$2_old)
                         (tobool$2_0 (distinct i.0$2_0 0)))
                        (=>
                           tobool$2_0
                           (let
                              ((HEAP$2 HEAP$2))
                              (forall
                                 ((call3$1_0 Int)
                                  (call1$2_0 Int)
                                  (HEAP$1_res (Array Int Int))
                                  (HEAP$2_res (Array Int Int)))
                                 (=>
                                    (INV_REC_memcmp^memcmp cur.0$1_0 needle$1_0 nl$1_0 HEAP$1 haystack.addr.0$2_0 needle$2_0 nl$2_0 HEAP$2 call3$1_0 call1$2_0 HEAP$1_res HEAP$2_res)
                                    (let
                                       ((HEAP$1 HEAP$1_res)
                                        (cmp4$1_0 (= call3$1_0 0)))
                                       (=>
                                          (not cmp4$1_0)
                                          (let
                                             ((incdec.ptr$1_0 (+ cur.0$1_0 1)))
                                             (let
                                                ((cur.0$1_0 incdec.ptr$1_0)
                                                 (HEAP$2 HEAP$2_res)
                                                 (tobool2$2_0 (distinct call1$2_0 0)))
                                                (=>
                                                   tobool2$2_0
                                                   (let
                                                      ((incdec.ptr$2_0 (+ haystack.addr.0$2_0 1))
                                                       (dec$2_0 (+ i.0$2_0 (- 1))))
                                                      (let
                                                         ((i.0$2_0 dec$2_0)
                                                          (haystack.addr.0$2_0 incdec.ptr$2_0))
                                                         (INV_MAIN_42 add.ptr1$1_0 cur.0$1_0 needle$1_0 nl$1_0 HEAP$1 haystack.addr.0$2_0 i.0$2_0 needle$2_0 nl$2_0 HEAP$2))))))))))))))))))))
(assert
   (forall
      ((add.ptr1$1_0_old Int)
       (cur.0$1_0_old Int)
       (needle$1_0_old Int)
       (nl$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (haystack.addr.0$2_0_old Int)
       (i.0$2_0_old Int)
       (needle$2_0_old Int)
       (nl$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 add.ptr1$1_0_old cur.0$1_0_old needle$1_0_old nl$1_0_old HEAP$1_old haystack.addr.0$2_0_old i.0$2_0_old needle$2_0_old nl$2_0_old HEAP$2_old)
         (let
            ((add.ptr1$1_0 add.ptr1$1_0_old)
             (cur.0$1_0 cur.0$1_0_old))
            (let
               ((needle$1_0 needle$1_0_old)
                (nl$1_0 nl$1_0_old)
                (HEAP$1 HEAP$1_old)
                (cmp2$1_0 (<= (abs cur.0$1_0) (abs add.ptr1$1_0))))
               (=>
                  cmp2$1_0
                  (let
                     ((HEAP$1 HEAP$1))
                     (forall
                        ((call3$1_0 Int)
                         (HEAP$1_res (Array Int Int)))
                        (=>
                           (INV_REC_memcmp__1 cur.0$1_0 needle$1_0 nl$1_0 HEAP$1 call3$1_0 HEAP$1_res)
                           (let
                              ((HEAP$1 HEAP$1_res)
                               (cmp4$1_0 (= call3$1_0 0)))
                              (=>
                                 (not cmp4$1_0)
                                 (let
                                    ((incdec.ptr$1_0 (+ cur.0$1_0 1)))
                                    (let
                                       ((cur.0$1_0 incdec.ptr$1_0))
                                       (=>
                                          (let
                                             ((haystack.addr.0$2_0 haystack.addr.0$2_0_old)
                                              (i.0$2_0 i.0$2_0_old))
                                             (let
                                                ((needle$2_0 needle$2_0_old)
                                                 (nl$2_0 nl$2_0_old)
                                                 (HEAP$2 HEAP$2_old)
                                                 (tobool$2_0 (distinct i.0$2_0 0)))
                                                (=>
                                                   tobool$2_0
                                                   (let
                                                      ((HEAP$2 HEAP$2))
                                                      (forall
                                                         ((call1$2_0 Int)
                                                          (HEAP$2_res (Array Int Int)))
                                                         (=>
                                                            (INV_REC_memcmp__2 haystack.addr.0$2_0 needle$2_0 nl$2_0 HEAP$2 call1$2_0 HEAP$2_res)
                                                            (let
                                                               ((HEAP$2 HEAP$2_res)
                                                                (tobool2$2_0 (distinct call1$2_0 0)))
                                                               (=>
                                                                  tobool2$2_0
                                                                  (let
                                                                     ((incdec.ptr$2_0 (+ haystack.addr.0$2_0 1))
                                                                      (dec$2_0 (+ i.0$2_0 (- 1))))
                                                                     (let
                                                                        ((i.0$2_0 dec$2_0)
                                                                         (haystack.addr.0$2_0 incdec.ptr$2_0))
                                                                        false))))))))))
                                          (INV_MAIN_42 add.ptr1$1_0 cur.0$1_0 needle$1_0 nl$1_0 HEAP$1 haystack.addr.0$2_0_old i.0$2_0_old needle$2_0_old nl$2_0_old HEAP$2_old)))))))))))))))
(assert
   (forall
      ((add.ptr1$1_0_old Int)
       (cur.0$1_0_old Int)
       (needle$1_0_old Int)
       (nl$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (haystack.addr.0$2_0_old Int)
       (i.0$2_0_old Int)
       (needle$2_0_old Int)
       (nl$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (INV_MAIN_42 add.ptr1$1_0_old cur.0$1_0_old needle$1_0_old nl$1_0_old HEAP$1_old haystack.addr.0$2_0_old i.0$2_0_old needle$2_0_old nl$2_0_old HEAP$2_old)
         (let
            ((haystack.addr.0$2_0 haystack.addr.0$2_0_old)
             (i.0$2_0 i.0$2_0_old))
            (let
               ((needle$2_0 needle$2_0_old)
                (nl$2_0 nl$2_0_old)
                (HEAP$2 HEAP$2_old)
                (tobool$2_0 (distinct i.0$2_0 0)))
               (=>
                  tobool$2_0
                  (let
                     ((HEAP$2 HEAP$2))
                     (forall
                        ((call1$2_0 Int)
                         (HEAP$2_res (Array Int Int)))
                        (=>
                           (INV_REC_memcmp__2 haystack.addr.0$2_0 needle$2_0 nl$2_0 HEAP$2 call1$2_0 HEAP$2_res)
                           (let
                              ((HEAP$2 HEAP$2_res)
                               (tobool2$2_0 (distinct call1$2_0 0)))
                              (=>
                                 tobool2$2_0
                                 (let
                                    ((incdec.ptr$2_0 (+ haystack.addr.0$2_0 1))
                                     (dec$2_0 (+ i.0$2_0 (- 1))))
                                    (let
                                       ((i.0$2_0 dec$2_0)
                                        (haystack.addr.0$2_0 incdec.ptr$2_0))
                                       (=>
                                          (let
                                             ((add.ptr1$1_0 add.ptr1$1_0_old)
                                              (cur.0$1_0 cur.0$1_0_old))
                                             (let
                                                ((needle$1_0 needle$1_0_old)
                                                 (nl$1_0 nl$1_0_old)
                                                 (HEAP$1 HEAP$1_old)
                                                 (cmp2$1_0 (<= (abs cur.0$1_0) (abs add.ptr1$1_0))))
                                                (=>
                                                   cmp2$1_0
                                                   (let
                                                      ((HEAP$1 HEAP$1))
                                                      (forall
                                                         ((call3$1_0 Int)
                                                          (HEAP$1_res (Array Int Int)))
                                                         (=>
                                                            (INV_REC_memcmp__1 cur.0$1_0 needle$1_0 nl$1_0 HEAP$1 call3$1_0 HEAP$1_res)
                                                            (let
                                                               ((HEAP$1 HEAP$1_res)
                                                                (cmp4$1_0 (= call3$1_0 0)))
                                                               (=>
                                                                  (not cmp4$1_0)
                                                                  (let
                                                                     ((incdec.ptr$1_0 (+ cur.0$1_0 1)))
                                                                     (let
                                                                        ((cur.0$1_0 incdec.ptr$1_0))
                                                                        false))))))))))
                                          (INV_MAIN_42 add.ptr1$1_0_old cur.0$1_0_old needle$1_0_old nl$1_0_old HEAP$1_old haystack.addr.0$2_0 i.0$2_0 needle$2_0 nl$2_0 HEAP$2)))))))))))))))
(check-sat)
(get-model)
