;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   __curbrk$1
   ()
   Int
   (- 9))
(define-fun
   __curbrk$2
   ()
   Int
   (- 9))
(define-fun
   INV_REC___libc_brk^__libc_brk
   ((_$1_0 Int)
    (HEAP$1 (Array Int Int))
    (_$2_0 Int)
    (HEAP$2 (Array Int Int))
    (result$1 Int)
    (result$2 Int)
    (HEAP$1_res (Array Int Int))
    (HEAP$2_res (Array Int Int)))
   Bool
   (=>
      (and
         (= _$1_0 _$2_0)
         (forall
            ((i Int))
            (= (select HEAP$1 i) (select HEAP$2 i))))
      (and
         (= result$1 result$2)
         (forall
            ((i Int))
            (= (select HEAP$1_res i) (select HEAP$2_res i))))))
(define-fun
   INV_REC___libc_brk__1
   ((_$1_0 Int)
    (HEAP (Array Int Int))
    (result$1 Int)
    (HEAP$1_res (Array Int Int)))
   Bool
   true)
(define-fun
   INV_REC___set_errno__1
   ((_$1_0 Int)
    (HEAP (Array Int Int))
    (result$1 Int)
    (HEAP$1_res (Array Int Int)))
   Bool
   true)
(define-fun
   INV_REC___libc_brk__2
   ((_$2_0 Int)
    (HEAP (Array Int Int))
    (result$2 Int)
    (HEAP$2_res (Array Int Int)))
   Bool
   true)
(define-fun
   IN_INV
   ((increment$1_0 Int)
    (HEAP$1 (Array Int Int))
    (increment$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= increment$1_0 increment$2_0)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= result$1 result$2)
      (forall
         ((i Int))
         (= (select HEAP$1 i) (select HEAP$2 i)))))
; :annot (INV_MAIN_0 increment$1_0 HEAP$1 increment$2_0 HEAP$2)
(declare-fun
   INV_MAIN_0
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((HEAP$2 HEAP$2))
                                    (forall
                                       ((call$1_0 Int)
                                        (call$2_0 Int)
                                        (HEAP$1_res (Array Int Int))
                                        (HEAP$2_res (Array Int Int)))
                                       (=>
                                          (INV_REC___libc_brk^__libc_brk 0 HEAP$1 0 HEAP$2 call$1_0 call$2_0 HEAP$1_res HEAP$2_res)
                                          (let
                                             ((HEAP$1 HEAP$1_res)
                                              (cmp1$1_0 (< call$1_0 0)))
                                             (=>
                                                cmp1$1_0
                                                (let
                                                   ((retval.0$1_0 (- 1)))
                                                   (let
                                                      ((result$1 retval.0$1_0)
                                                       (HEAP$1_res HEAP$1)
                                                       (HEAP$2 HEAP$2_res)
                                                       (cmp1$2_0 (< call$2_0 0)))
                                                      (=>
                                                         (not cmp1$2_0)
                                                         (let
                                                            ((cmp4$2_0 (= increment$2_0 0)))
                                                            (not (not cmp4$2_0))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 (not cmp$2_0)
                                 (let
                                    ((cmp4$2_0 (= increment$2_0 0)))
                                    (=>
                                       (not cmp4$2_0)
                                       (forall
                                          ((call$1_0 Int)
                                           (HEAP$1_res (Array Int Int)))
                                          (=>
                                             (INV_REC___libc_brk__1 0 HEAP$1 call$1_0 HEAP$1_res)
                                             (let
                                                ((HEAP$1 HEAP$1_res)
                                                 (cmp1$1_0 (< call$1_0 0)))
                                                (=>
                                                   cmp1$1_0
                                                   (let
                                                      ((retval.0$1_0 (- 1)))
                                                      (let
                                                         ((result$1 retval.0$1_0)
                                                          (HEAP$1_res HEAP$1))
                                                         false)))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((HEAP$2 HEAP$2))
                                    (forall
                                       ((call$1_0 Int)
                                        (call$2_0 Int)
                                        (HEAP$1_res (Array Int Int))
                                        (HEAP$2_res (Array Int Int)))
                                       (=>
                                          (INV_REC___libc_brk^__libc_brk 0 HEAP$1 0 HEAP$2 call$1_0 call$2_0 HEAP$1_res HEAP$2_res)
                                          (let
                                             ((HEAP$1 HEAP$1_res)
                                              (cmp1$1_0 (< call$1_0 0)))
                                             (=>
                                                (not cmp1$1_0)
                                                (let
                                                   ((cmp4$1_0 (= increment$1_0 0)))
                                                   (=>
                                                      cmp4$1_0
                                                      (let
                                                         ((_$1_1 (select HEAP$1 __curbrk$1)))
                                                         (let
                                                            ((retval.0$1_0 _$1_1))
                                                            (let
                                                               ((result$1 retval.0$1_0)
                                                                (HEAP$1_res HEAP$1)
                                                                (HEAP$2 HEAP$2_res)
                                                                (cmp1$2_0 (< call$2_0 0)))
                                                               (=>
                                                                  (not cmp1$2_0)
                                                                  (let
                                                                     ((cmp4$2_0 (= increment$2_0 0)))
                                                                     (not (not cmp4$2_0)))))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 (not cmp$2_0)
                                 (let
                                    ((cmp4$2_0 (= increment$2_0 0)))
                                    (=>
                                       (not cmp4$2_0)
                                       (forall
                                          ((call$1_0 Int)
                                           (HEAP$1_res (Array Int Int)))
                                          (=>
                                             (INV_REC___libc_brk__1 0 HEAP$1 call$1_0 HEAP$1_res)
                                             (let
                                                ((HEAP$1 HEAP$1_res)
                                                 (cmp1$1_0 (< call$1_0 0)))
                                                (=>
                                                   (not cmp1$1_0)
                                                   (let
                                                      ((cmp4$1_0 (= increment$1_0 0)))
                                                      (=>
                                                         cmp4$1_0
                                                         (let
                                                            ((_$1_1 (select HEAP$1 __curbrk$1)))
                                                            (let
                                                               ((retval.0$1_0 _$1_1))
                                                               (let
                                                                  ((result$1 retval.0$1_0)
                                                                   (HEAP$1_res HEAP$1))
                                                                  false))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     (not cmp$1_0)
                     (let
                        ((cmp4$1_0 (= increment$1_0 0)))
                        (=>
                           cmp4$1_0
                           (let
                              ((_$1_1 (select HEAP$1 __curbrk$1)))
                              (let
                                 ((retval.0$1_0 _$1_1))
                                 (let
                                    ((result$1 retval.0$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (increment$2_0 increment$2_0_old)
                                     (HEAP$2 HEAP$2_old))
                                    (let
                                       ((_$2_0 (select HEAP$2 __curbrk$2)))
                                       (let
                                          ((cmp$2_0 (= _$2_0 0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((HEAP$2 HEAP$2))
                                                (forall
                                                   ((call$2_0 Int)
                                                    (HEAP$2_res (Array Int Int)))
                                                   (=>
                                                      (INV_REC___libc_brk__2 0 HEAP$2 call$2_0 HEAP$2_res)
                                                      (let
                                                         ((HEAP$2 HEAP$2_res)
                                                          (cmp1$2_0 (< call$2_0 0)))
                                                         (=>
                                                            (not cmp1$2_0)
                                                            (let
                                                               ((cmp4$2_0 (= increment$2_0 0)))
                                                               (not (not cmp4$2_0)))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     (not cmp$1_0)
                     (let
                        ((cmp4$1_0 (= increment$1_0 0)))
                        (=>
                           cmp4$1_0
                           (let
                              ((_$1_1 (select HEAP$1 __curbrk$1)))
                              (let
                                 ((retval.0$1_0 _$1_1))
                                 (let
                                    ((result$1 retval.0$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (increment$2_0 increment$2_0_old)
                                     (HEAP$2 HEAP$2_old))
                                    (let
                                       ((_$2_0 (select HEAP$2 __curbrk$2)))
                                       (let
                                          ((cmp$2_0 (= _$2_0 0)))
                                          (=>
                                             (not cmp$2_0)
                                             (let
                                                ((cmp4$2_0 (= increment$2_0 0)))
                                                (not (not cmp4$2_0))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((HEAP$2 HEAP$2))
                                    (forall
                                       ((call$1_0 Int)
                                        (call$2_0 Int)
                                        (HEAP$1_res (Array Int Int))
                                        (HEAP$2_res (Array Int Int)))
                                       (=>
                                          (INV_REC___libc_brk^__libc_brk 0 HEAP$1 0 HEAP$2 call$1_0 call$2_0 HEAP$1_res HEAP$2_res)
                                          (let
                                             ((HEAP$1 HEAP$1_res)
                                              (cmp1$1_0 (< call$1_0 0)))
                                             (=>
                                                (not cmp1$1_0)
                                                (let
                                                   ((cmp4$1_0 (= increment$1_0 0)))
                                                   (=>
                                                      (not cmp4$1_0)
                                                      (let
                                                         ((HEAP$2 HEAP$2_res)
                                                          (cmp1$2_0 (< call$2_0 0)))
                                                         (=>
                                                            cmp1$2_0
                                                            (let
                                                               ((retval.0$2_0 (- 1)))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  false))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((HEAP$2 HEAP$2))
                                    (forall
                                       ((call$1_0 Int)
                                        (call$2_0 Int)
                                        (HEAP$1_res (Array Int Int))
                                        (HEAP$2_res (Array Int Int)))
                                       (=>
                                          (INV_REC___libc_brk^__libc_brk 0 HEAP$1 0 HEAP$2 call$1_0 call$2_0 HEAP$1_res HEAP$2_res)
                                          (let
                                             ((HEAP$1 HEAP$1_res)
                                              (cmp1$1_0 (< call$1_0 0)))
                                             (=>
                                                (not cmp1$1_0)
                                                (let
                                                   ((cmp4$1_0 (= increment$1_0 0)))
                                                   (=>
                                                      (not cmp4$1_0)
                                                      (let
                                                         ((HEAP$2 HEAP$2_res)
                                                          (cmp1$2_0 (< call$2_0 0)))
                                                         (=>
                                                            (not cmp1$2_0)
                                                            (let
                                                               ((cmp4$2_0 (= increment$2_0 0)))
                                                               (=>
                                                                  cmp4$2_0
                                                                  (let
                                                                     ((_$2_1 (select HEAP$2 __curbrk$2)))
                                                                     (let
                                                                        ((retval.0$2_0 _$2_1))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           false)))))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 (not cmp$2_0)
                                 (let
                                    ((cmp4$2_0 (= increment$2_0 0)))
                                    (=>
                                       cmp4$2_0
                                       (let
                                          ((_$2_1 (select HEAP$2 __curbrk$2)))
                                          (let
                                             ((retval.0$2_0 _$2_1))
                                             (let
                                                ((result$2 retval.0$2_0)
                                                 (HEAP$2_res HEAP$2))
                                                (forall
                                                   ((call$1_0 Int)
                                                    (HEAP$1_res (Array Int Int)))
                                                   (=>
                                                      (INV_REC___libc_brk__1 0 HEAP$1 call$1_0 HEAP$1_res)
                                                      (let
                                                         ((HEAP$1 HEAP$1_res)
                                                          (cmp1$1_0 (< call$1_0 0)))
                                                         (=>
                                                            (not cmp1$1_0)
                                                            (let
                                                               ((cmp4$1_0 (= increment$1_0 0)))
                                                               (not (not cmp4$1_0)))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     (not cmp$1_0)
                     (let
                        ((cmp4$1_0 (= increment$1_0 0)))
                        (=>
                           (not cmp4$1_0)
                           (let
                              ((increment$2_0 increment$2_0_old)
                               (HEAP$2 HEAP$2_old))
                              (let
                                 ((_$2_0 (select HEAP$2 __curbrk$2)))
                                 (let
                                    ((cmp$2_0 (= _$2_0 0)))
                                    (=>
                                       cmp$2_0
                                       (let
                                          ((HEAP$2 HEAP$2))
                                          (forall
                                             ((call$2_0 Int)
                                              (HEAP$2_res (Array Int Int)))
                                             (=>
                                                (INV_REC___libc_brk__2 0 HEAP$2 call$2_0 HEAP$2_res)
                                                (let
                                                   ((HEAP$2 HEAP$2_res)
                                                    (cmp1$2_0 (< call$2_0 0)))
                                                   (=>
                                                      cmp1$2_0
                                                      (let
                                                         ((retval.0$2_0 (- 1)))
                                                         (let
                                                            ((result$2 retval.0$2_0)
                                                             (HEAP$2_res HEAP$2))
                                                            false))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     (not cmp$1_0)
                     (let
                        ((cmp4$1_0 (= increment$1_0 0)))
                        (=>
                           (not cmp4$1_0)
                           (let
                              ((increment$2_0 increment$2_0_old)
                               (HEAP$2 HEAP$2_old))
                              (let
                                 ((_$2_0 (select HEAP$2 __curbrk$2)))
                                 (let
                                    ((cmp$2_0 (= _$2_0 0)))
                                    (=>
                                       cmp$2_0
                                       (let
                                          ((HEAP$2 HEAP$2))
                                          (forall
                                             ((call$2_0 Int)
                                              (HEAP$2_res (Array Int Int)))
                                             (=>
                                                (INV_REC___libc_brk__2 0 HEAP$2 call$2_0 HEAP$2_res)
                                                (let
                                                   ((HEAP$2 HEAP$2_res)
                                                    (cmp1$2_0 (< call$2_0 0)))
                                                   (=>
                                                      (not cmp1$2_0)
                                                      (let
                                                         ((cmp4$2_0 (= increment$2_0 0)))
                                                         (=>
                                                            cmp4$2_0
                                                            (let
                                                               ((_$2_1 (select HEAP$2 __curbrk$2)))
                                                               (let
                                                                  ((retval.0$2_0 _$2_1))
                                                                  (let
                                                                     ((result$2 retval.0$2_0)
                                                                      (HEAP$2_res HEAP$2))
                                                                     false)))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     (not cmp$1_0)
                     (let
                        ((cmp4$1_0 (= increment$1_0 0)))
                        (=>
                           (not cmp4$1_0)
                           (let
                              ((increment$2_0 increment$2_0_old)
                               (HEAP$2 HEAP$2_old))
                              (let
                                 ((_$2_0 (select HEAP$2 __curbrk$2)))
                                 (let
                                    ((cmp$2_0 (= _$2_0 0)))
                                    (=>
                                       (not cmp$2_0)
                                       (let
                                          ((cmp4$2_0 (= increment$2_0 0)))
                                          (=>
                                             cmp4$2_0
                                             (let
                                                ((_$2_1 (select HEAP$2 __curbrk$2)))
                                                (let
                                                   ((retval.0$2_0 _$2_1))
                                                   (let
                                                      ((result$2 retval.0$2_0)
                                                       (HEAP$2_res HEAP$2))
                                                      false))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((HEAP$2 HEAP$2))
                                    (forall
                                       ((call$1_0 Int)
                                        (call$2_0 Int)
                                        (HEAP$1_res (Array Int Int))
                                        (HEAP$2_res (Array Int Int)))
                                       (=>
                                          (INV_REC___libc_brk^__libc_brk 0 HEAP$1 0 HEAP$2 call$1_0 call$2_0 HEAP$1_res HEAP$2_res)
                                          (let
                                             ((HEAP$1 HEAP$1_res)
                                              (cmp1$1_0 (< call$1_0 0)))
                                             (=>
                                                cmp1$1_0
                                                (let
                                                   ((retval.0$1_0 (- 1)))
                                                   (let
                                                      ((result$1 retval.0$1_0)
                                                       (HEAP$1_res HEAP$1)
                                                       (HEAP$2 HEAP$2_res)
                                                       (cmp1$2_0 (< call$2_0 0)))
                                                      (=>
                                                         cmp1$2_0
                                                         (let
                                                            ((retval.0$2_0 (- 1)))
                                                            (let
                                                               ((result$2 retval.0$2_0)
                                                                (HEAP$2_res HEAP$2))
                                                               (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((HEAP$2 HEAP$2))
                                    (forall
                                       ((call$1_0 Int)
                                        (call$2_0 Int)
                                        (HEAP$1_res (Array Int Int))
                                        (HEAP$2_res (Array Int Int)))
                                       (=>
                                          (INV_REC___libc_brk^__libc_brk 0 HEAP$1 0 HEAP$2 call$1_0 call$2_0 HEAP$1_res HEAP$2_res)
                                          (let
                                             ((HEAP$1 HEAP$1_res)
                                              (cmp1$1_0 (< call$1_0 0)))
                                             (=>
                                                cmp1$1_0
                                                (let
                                                   ((retval.0$1_0 (- 1)))
                                                   (let
                                                      ((result$1 retval.0$1_0)
                                                       (HEAP$1_res HEAP$1)
                                                       (HEAP$2 HEAP$2_res)
                                                       (cmp1$2_0 (< call$2_0 0)))
                                                      (=>
                                                         (not cmp1$2_0)
                                                         (let
                                                            ((cmp4$2_0 (= increment$2_0 0)))
                                                            (=>
                                                               cmp4$2_0
                                                               (let
                                                                  ((_$2_1 (select HEAP$2 __curbrk$2)))
                                                                  (let
                                                                     ((retval.0$2_0 _$2_1))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 (not cmp$2_0)
                                 (let
                                    ((cmp4$2_0 (= increment$2_0 0)))
                                    (=>
                                       cmp4$2_0
                                       (let
                                          ((_$2_1 (select HEAP$2 __curbrk$2)))
                                          (let
                                             ((retval.0$2_0 _$2_1))
                                             (let
                                                ((result$2 retval.0$2_0)
                                                 (HEAP$2_res HEAP$2))
                                                (forall
                                                   ((call$1_0 Int)
                                                    (HEAP$1_res (Array Int Int)))
                                                   (=>
                                                      (INV_REC___libc_brk__1 0 HEAP$1 call$1_0 HEAP$1_res)
                                                      (let
                                                         ((HEAP$1 HEAP$1_res)
                                                          (cmp1$1_0 (< call$1_0 0)))
                                                         (=>
                                                            cmp1$1_0
                                                            (let
                                                               ((retval.0$1_0 (- 1)))
                                                               (let
                                                                  ((result$1 retval.0$1_0)
                                                                   (HEAP$1_res HEAP$1))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((HEAP$2 HEAP$2))
                                    (forall
                                       ((call$1_0 Int)
                                        (call$2_0 Int)
                                        (HEAP$1_res (Array Int Int))
                                        (HEAP$2_res (Array Int Int)))
                                       (=>
                                          (INV_REC___libc_brk^__libc_brk 0 HEAP$1 0 HEAP$2 call$1_0 call$2_0 HEAP$1_res HEAP$2_res)
                                          (let
                                             ((HEAP$1 HEAP$1_res)
                                              (cmp1$1_0 (< call$1_0 0)))
                                             (=>
                                                (not cmp1$1_0)
                                                (let
                                                   ((cmp4$1_0 (= increment$1_0 0)))
                                                   (=>
                                                      cmp4$1_0
                                                      (let
                                                         ((_$1_1 (select HEAP$1 __curbrk$1)))
                                                         (let
                                                            ((retval.0$1_0 _$1_1))
                                                            (let
                                                               ((result$1 retval.0$1_0)
                                                                (HEAP$1_res HEAP$1)
                                                                (HEAP$2 HEAP$2_res)
                                                                (cmp1$2_0 (< call$2_0 0)))
                                                               (=>
                                                                  cmp1$2_0
                                                                  (let
                                                                     ((retval.0$2_0 (- 1)))
                                                                     (let
                                                                        ((result$2 retval.0$2_0)
                                                                         (HEAP$2_res HEAP$2))
                                                                        (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((HEAP$2 HEAP$2))
                                    (forall
                                       ((call$1_0 Int)
                                        (call$2_0 Int)
                                        (HEAP$1_res (Array Int Int))
                                        (HEAP$2_res (Array Int Int)))
                                       (=>
                                          (INV_REC___libc_brk^__libc_brk 0 HEAP$1 0 HEAP$2 call$1_0 call$2_0 HEAP$1_res HEAP$2_res)
                                          (let
                                             ((HEAP$1 HEAP$1_res)
                                              (cmp1$1_0 (< call$1_0 0)))
                                             (=>
                                                (not cmp1$1_0)
                                                (let
                                                   ((cmp4$1_0 (= increment$1_0 0)))
                                                   (=>
                                                      cmp4$1_0
                                                      (let
                                                         ((_$1_1 (select HEAP$1 __curbrk$1)))
                                                         (let
                                                            ((retval.0$1_0 _$1_1))
                                                            (let
                                                               ((result$1 retval.0$1_0)
                                                                (HEAP$1_res HEAP$1)
                                                                (HEAP$2 HEAP$2_res)
                                                                (cmp1$2_0 (< call$2_0 0)))
                                                               (=>
                                                                  (not cmp1$2_0)
                                                                  (let
                                                                     ((cmp4$2_0 (= increment$2_0 0)))
                                                                     (=>
                                                                        cmp4$2_0
                                                                        (let
                                                                           ((_$2_1 (select HEAP$2 __curbrk$2)))
                                                                           (let
                                                                              ((retval.0$2_0 _$2_1))
                                                                              (let
                                                                                 ((result$2 retval.0$2_0)
                                                                                  (HEAP$2_res HEAP$2))
                                                                                 (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 (not cmp$2_0)
                                 (let
                                    ((cmp4$2_0 (= increment$2_0 0)))
                                    (=>
                                       cmp4$2_0
                                       (let
                                          ((_$2_1 (select HEAP$2 __curbrk$2)))
                                          (let
                                             ((retval.0$2_0 _$2_1))
                                             (let
                                                ((result$2 retval.0$2_0)
                                                 (HEAP$2_res HEAP$2))
                                                (forall
                                                   ((call$1_0 Int)
                                                    (HEAP$1_res (Array Int Int)))
                                                   (=>
                                                      (INV_REC___libc_brk__1 0 HEAP$1 call$1_0 HEAP$1_res)
                                                      (let
                                                         ((HEAP$1 HEAP$1_res)
                                                          (cmp1$1_0 (< call$1_0 0)))
                                                         (=>
                                                            (not cmp1$1_0)
                                                            (let
                                                               ((cmp4$1_0 (= increment$1_0 0)))
                                                               (=>
                                                                  cmp4$1_0
                                                                  (let
                                                                     ((_$1_1 (select HEAP$1 __curbrk$1)))
                                                                     (let
                                                                        ((retval.0$1_0 _$1_1))
                                                                        (let
                                                                           ((result$1 retval.0$1_0)
                                                                            (HEAP$1_res HEAP$1))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     (not cmp$1_0)
                     (let
                        ((cmp4$1_0 (= increment$1_0 0)))
                        (=>
                           cmp4$1_0
                           (let
                              ((_$1_1 (select HEAP$1 __curbrk$1)))
                              (let
                                 ((retval.0$1_0 _$1_1))
                                 (let
                                    ((result$1 retval.0$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (increment$2_0 increment$2_0_old)
                                     (HEAP$2 HEAP$2_old))
                                    (let
                                       ((_$2_0 (select HEAP$2 __curbrk$2)))
                                       (let
                                          ((cmp$2_0 (= _$2_0 0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((HEAP$2 HEAP$2))
                                                (forall
                                                   ((call$2_0 Int)
                                                    (HEAP$2_res (Array Int Int)))
                                                   (=>
                                                      (INV_REC___libc_brk__2 0 HEAP$2 call$2_0 HEAP$2_res)
                                                      (let
                                                         ((HEAP$2 HEAP$2_res)
                                                          (cmp1$2_0 (< call$2_0 0)))
                                                         (=>
                                                            cmp1$2_0
                                                            (let
                                                               ((retval.0$2_0 (- 1)))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     (not cmp$1_0)
                     (let
                        ((cmp4$1_0 (= increment$1_0 0)))
                        (=>
                           cmp4$1_0
                           (let
                              ((_$1_1 (select HEAP$1 __curbrk$1)))
                              (let
                                 ((retval.0$1_0 _$1_1))
                                 (let
                                    ((result$1 retval.0$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (increment$2_0 increment$2_0_old)
                                     (HEAP$2 HEAP$2_old))
                                    (let
                                       ((_$2_0 (select HEAP$2 __curbrk$2)))
                                       (let
                                          ((cmp$2_0 (= _$2_0 0)))
                                          (=>
                                             cmp$2_0
                                             (let
                                                ((HEAP$2 HEAP$2))
                                                (forall
                                                   ((call$2_0 Int)
                                                    (HEAP$2_res (Array Int Int)))
                                                   (=>
                                                      (INV_REC___libc_brk__2 0 HEAP$2 call$2_0 HEAP$2_res)
                                                      (let
                                                         ((HEAP$2 HEAP$2_res)
                                                          (cmp1$2_0 (< call$2_0 0)))
                                                         (=>
                                                            (not cmp1$2_0)
                                                            (let
                                                               ((cmp4$2_0 (= increment$2_0 0)))
                                                               (=>
                                                                  cmp4$2_0
                                                                  (let
                                                                     ((_$2_1 (select HEAP$2 __curbrk$2)))
                                                                     (let
                                                                        ((retval.0$2_0 _$2_1))
                                                                        (let
                                                                           ((result$2 retval.0$2_0)
                                                                            (HEAP$2_res HEAP$2))
                                                                           (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     (not cmp$1_0)
                     (let
                        ((cmp4$1_0 (= increment$1_0 0)))
                        (=>
                           cmp4$1_0
                           (let
                              ((_$1_1 (select HEAP$1 __curbrk$1)))
                              (let
                                 ((retval.0$1_0 _$1_1))
                                 (let
                                    ((result$1 retval.0$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (increment$2_0 increment$2_0_old)
                                     (HEAP$2 HEAP$2_old))
                                    (let
                                       ((_$2_0 (select HEAP$2 __curbrk$2)))
                                       (let
                                          ((cmp$2_0 (= _$2_0 0)))
                                          (=>
                                             (not cmp$2_0)
                                             (let
                                                ((cmp4$2_0 (= increment$2_0 0)))
                                                (=>
                                                   cmp4$2_0
                                                   (let
                                                      ((_$2_1 (select HEAP$2 __curbrk$2)))
                                                      (let
                                                         ((retval.0$2_0 _$2_1))
                                                         (let
                                                            ((result$2 retval.0$2_0)
                                                             (HEAP$2_res HEAP$2))
                                                            (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 cmp$2_0
                                 (let
                                    ((HEAP$2 HEAP$2))
                                    (forall
                                       ((call$1_0 Int)
                                        (call$2_0 Int)
                                        (HEAP$1_res (Array Int Int))
                                        (HEAP$2_res (Array Int Int)))
                                       (=>
                                          (INV_REC___libc_brk^__libc_brk 0 HEAP$1 0 HEAP$2 call$1_0 call$2_0 HEAP$1_res HEAP$2_res)
                                          (let
                                             ((HEAP$1 HEAP$1_res)
                                              (cmp1$1_0 (< call$1_0 0)))
                                             (=>
                                                (not cmp1$1_0)
                                                (let
                                                   ((cmp4$1_0 (= increment$1_0 0)))
                                                   (=>
                                                      (not cmp4$1_0)
                                                      (let
                                                         ((HEAP$2 HEAP$2_res)
                                                          (cmp1$2_0 (< call$2_0 0)))
                                                         (=>
                                                            (not cmp1$2_0)
                                                            (let
                                                               ((cmp4$2_0 (= increment$2_0 0)))
                                                               (=>
                                                                  (not cmp4$2_0)
                                                                  (forall
                                                                     ((i1 Int)
                                                                      (i2 Int))
                                                                     (INV_MAIN_0 increment$1_0 i1 (select HEAP$1 i1) increment$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     cmp$1_0
                     (let
                        ((HEAP$1 HEAP$1)
                         (increment$2_0 increment$2_0_old)
                         (HEAP$2 HEAP$2_old))
                        (let
                           ((_$2_0 (select HEAP$2 __curbrk$2)))
                           (let
                              ((cmp$2_0 (= _$2_0 0)))
                              (=>
                                 (not cmp$2_0)
                                 (let
                                    ((cmp4$2_0 (= increment$2_0 0)))
                                    (=>
                                       (not cmp4$2_0)
                                       (forall
                                          ((call$1_0 Int)
                                           (HEAP$1_res (Array Int Int)))
                                          (=>
                                             (INV_REC___libc_brk__1 0 HEAP$1 call$1_0 HEAP$1_res)
                                             (let
                                                ((HEAP$1 HEAP$1_res)
                                                 (cmp1$1_0 (< call$1_0 0)))
                                                (=>
                                                   (not cmp1$1_0)
                                                   (let
                                                      ((cmp4$1_0 (= increment$1_0 0)))
                                                      (=>
                                                         (not cmp4$1_0)
                                                         (forall
                                                            ((i1 Int)
                                                             (i2 Int))
                                                            (INV_MAIN_0 increment$1_0 i1 (select HEAP$1 i1) increment$2_0 i2 (select HEAP$2 i2))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     (not cmp$1_0)
                     (let
                        ((cmp4$1_0 (= increment$1_0 0)))
                        (=>
                           (not cmp4$1_0)
                           (let
                              ((increment$2_0 increment$2_0_old)
                               (HEAP$2 HEAP$2_old))
                              (let
                                 ((_$2_0 (select HEAP$2 __curbrk$2)))
                                 (let
                                    ((cmp$2_0 (= _$2_0 0)))
                                    (=>
                                       cmp$2_0
                                       (let
                                          ((HEAP$2 HEAP$2))
                                          (forall
                                             ((call$2_0 Int)
                                              (HEAP$2_res (Array Int Int)))
                                             (=>
                                                (INV_REC___libc_brk__2 0 HEAP$2 call$2_0 HEAP$2_res)
                                                (let
                                                   ((HEAP$2 HEAP$2_res)
                                                    (cmp1$2_0 (< call$2_0 0)))
                                                   (=>
                                                      (not cmp1$2_0)
                                                      (let
                                                         ((cmp4$2_0 (= increment$2_0 0)))
                                                         (=>
                                                            (not cmp4$2_0)
                                                            (forall
                                                               ((i1 Int)
                                                                (i2 Int))
                                                               (INV_MAIN_0 increment$1_0 i1 (select HEAP$1 i1) increment$2_0 i2 (select HEAP$2 i2)))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV increment$1_0_old HEAP$1_old increment$2_0_old HEAP$2_old)
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_0 (select HEAP$1 __curbrk$1)))
               (let
                  ((cmp$1_0 (= _$1_0 0)))
                  (=>
                     (not cmp$1_0)
                     (let
                        ((cmp4$1_0 (= increment$1_0 0)))
                        (=>
                           (not cmp4$1_0)
                           (let
                              ((increment$2_0 increment$2_0_old)
                               (HEAP$2 HEAP$2_old))
                              (let
                                 ((_$2_0 (select HEAP$2 __curbrk$2)))
                                 (let
                                    ((cmp$2_0 (= _$2_0 0)))
                                    (=>
                                       (not cmp$2_0)
                                       (let
                                          ((cmp4$2_0 (= increment$2_0 0)))
                                          (=>
                                             (not cmp4$2_0)
                                             (forall
                                                ((i1 Int)
                                                 (i2 Int))
                                                (INV_MAIN_0 increment$1_0 i1 (select HEAP$1 i1) increment$2_0 i2 (select HEAP$2 i2))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 increment$1_0_old i1_old (select HEAP$1_old i1_old) increment$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_2 (select HEAP$1 __curbrk$1))
                (cmp8$1_0 (> increment$1_0 0)))
               (=>
                  cmp8$1_0
                  (let
                     ((_$1_3 _$1_2))
                     (let
                        ((add$1_0 (+ _$1_3 increment$1_0))
                         (_$1_4 _$1_2))
                        (let
                           ((cmp9$1_0 (< add$1_0 _$1_4)))
                           (=>
                              cmp9$1_0
                              (let
                                 ((HEAP$1 HEAP$1)
                                  (increment$2_0 increment$2_0_old)
                                  (HEAP$2 HEAP$2_old))
                                 (let
                                    ((_$2_2 (select HEAP$2 __curbrk$2)))
                                    (let
                                       ((add.ptr$2_0 (+ _$2_2 increment$2_0))
                                        (HEAP$2 HEAP$2))
                                       (forall
                                          ((call8$2_0 Int)
                                           (HEAP$2_res (Array Int Int)))
                                          (=>
                                             (INV_REC___libc_brk__2 add.ptr$2_0 HEAP$2 call8$2_0 HEAP$2_res)
                                             (let
                                                ((HEAP$2 HEAP$2_res)
                                                 (cmp9$2_0 (< call8$2_0 0)))
                                                (let
                                                   ((.$2_0 (ite cmp9$2_0 (- 1) _$2_2)))
                                                   (let
                                                      ((retval.0$2_0 .$2_0))
                                                      (let
                                                         ((result$2 retval.0$2_0)
                                                          (HEAP$2_res HEAP$2))
                                                         (forall
                                                            ((call11$1_0 Int)
                                                             (HEAP$1_res (Array Int Int)))
                                                            (=>
                                                               (INV_REC___set_errno__1 42 HEAP$1 call11$1_0 HEAP$1_res)
                                                               (let
                                                                  ((HEAP$1 HEAP$1_res)
                                                                   (retval.0$1_0 (- 1)))
                                                                  (let
                                                                     ((result$1 retval.0$1_0)
                                                                      (HEAP$1_res HEAP$1))
                                                                     (OUT_INV result$1 result$2 HEAP$1 HEAP$2))))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 increment$1_0_old i1_old (select HEAP$1_old i1_old) increment$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_2 (select HEAP$1 __curbrk$1))
                (cmp8$1_0 (> increment$1_0 0)))
               (=>
                  cmp8$1_0
                  (let
                     ((_$1_3 _$1_2))
                     (let
                        ((add$1_0 (+ _$1_3 increment$1_0))
                         (_$1_4 _$1_2))
                        (let
                           ((cmp9$1_0 (< add$1_0 _$1_4)))
                           (=>
                              (not cmp9$1_0)
                              (let
                                 ((add.ptr$1_0 (+ _$1_2 increment$1_0))
                                  (HEAP$1 HEAP$1)
                                  (increment$2_0 increment$2_0_old)
                                  (HEAP$2 HEAP$2_old))
                                 (let
                                    ((_$2_2 (select HEAP$2 __curbrk$2)))
                                    (let
                                       ((add.ptr$2_0 (+ _$2_2 increment$2_0))
                                        (HEAP$2 HEAP$2))
                                       (forall
                                          ((call13$1_0 Int)
                                           (call8$2_0 Int)
                                           (HEAP$1_res (Array Int Int))
                                           (HEAP$2_res (Array Int Int)))
                                          (=>
                                             (INV_REC___libc_brk^__libc_brk add.ptr$1_0 HEAP$1 add.ptr$2_0 HEAP$2 call13$1_0 call8$2_0 HEAP$1_res HEAP$2_res)
                                             (let
                                                ((HEAP$1 HEAP$1_res)
                                                 (cmp14$1_0 (< call13$1_0 0)))
                                                (let
                                                   ((.$1_0 (ite cmp14$1_0 (- 1) _$1_2)))
                                                   (let
                                                      ((retval.0$1_0 .$1_0))
                                                      (let
                                                         ((result$1 retval.0$1_0)
                                                          (HEAP$1_res HEAP$1)
                                                          (HEAP$2 HEAP$2_res)
                                                          (cmp9$2_0 (< call8$2_0 0)))
                                                         (let
                                                            ((.$2_0 (ite cmp9$2_0 (- 1) _$2_2)))
                                                            (let
                                                               ((retval.0$2_0 .$2_0))
                                                               (let
                                                                  ((result$2 retval.0$2_0)
                                                                   (HEAP$2_res HEAP$2))
                                                                  (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))))))
(assert
   (forall
      ((increment$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (increment$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_MAIN_0 increment$1_0_old i1_old (select HEAP$1_old i1_old) increment$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((increment$1_0 increment$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((_$1_2 (select HEAP$1 __curbrk$1))
                (cmp8$1_0 (> increment$1_0 0)))
               (=>
                  (not cmp8$1_0)
                  (let
                     ((add.ptr$1_0 (+ _$1_2 increment$1_0))
                      (HEAP$1 HEAP$1)
                      (increment$2_0 increment$2_0_old)
                      (HEAP$2 HEAP$2_old))
                     (let
                        ((_$2_2 (select HEAP$2 __curbrk$2)))
                        (let
                           ((add.ptr$2_0 (+ _$2_2 increment$2_0))
                            (HEAP$2 HEAP$2))
                           (forall
                              ((call13$1_0 Int)
                               (call8$2_0 Int)
                               (HEAP$1_res (Array Int Int))
                               (HEAP$2_res (Array Int Int)))
                              (=>
                                 (INV_REC___libc_brk^__libc_brk add.ptr$1_0 HEAP$1 add.ptr$2_0 HEAP$2 call13$1_0 call8$2_0 HEAP$1_res HEAP$2_res)
                                 (let
                                    ((HEAP$1 HEAP$1_res)
                                     (cmp14$1_0 (< call13$1_0 0)))
                                    (let
                                       ((.$1_0 (ite cmp14$1_0 (- 1) _$1_2)))
                                       (let
                                          ((retval.0$1_0 .$1_0))
                                          (let
                                             ((result$1 retval.0$1_0)
                                              (HEAP$1_res HEAP$1)
                                              (HEAP$2 HEAP$2_res)
                                              (cmp9$2_0 (< call8$2_0 0)))
                                             (let
                                                ((.$2_0 (ite cmp9$2_0 (- 1) _$2_2)))
                                                (let
                                                   ((retval.0$2_0 .$2_0))
                                                   (let
                                                      ((result$2 retval.0$2_0)
                                                       (HEAP$2_res HEAP$2))
                                                      (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))))))
(check-sat)
(get-model)
