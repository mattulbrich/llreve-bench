;; Produced by llreve (commit dc2abeaa50d9197d51fa4223b58154246b164df0)
;; See https://formal.iti.kit.edu/reve and https://github.com/mattulbrich/llreve/
;; (c) 2018 KIT

(set-logic HORN)
(define-fun
   IN_INV
   ((a$1_0 Int)
    (b$1_0 Int)
    (HEAP$1 (Array Int Int))
    (a$2_0 Int)
    (b$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= a$1_0 a$2_0)
      (= b$1_0 b$2_0)
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
(declare-fun
   INV_REC_g^g
   (Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_g^g_PRE
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_g__1
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_g__1_PRE
   (Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_g__2
   (Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(declare-fun
   INV_REC_g__2_PRE
   (Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((a$1_0_old Int)
       (b$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (a$2_0_old Int)
       (b$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (IN_INV a$1_0_old b$1_0_old HEAP$1_old a$2_0_old b$2_0_old HEAP$2_old)
         (let
            ((a$1_0 a$1_0_old)
             (b$1_0 b$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((HEAP$1 HEAP$1)
                (a$2_0 a$2_0_old)
                (b$2_0 b$2_0_old)
                (HEAP$2 HEAP$2_old))
               (let
                  ((HEAP$2 HEAP$2))
                  (and
                     (forall
                        ((i1 Int)
                         (i2 Int))
                        (INV_REC_g^g_PRE b$1_0 i1 (select HEAP$1 i1) b$2_0 i2 (select HEAP$2 i2)))
                     (forall
                        ((call$1_0 Int)
                         (call$2_0 Int)
                         (HEAP$1_res (Array Int Int))
                         (HEAP$2_res (Array Int Int)))
                        (=>
                           (forall
                              ((i1 Int)
                               (i2 Int)
                               (i1_res Int)
                               (i2_res Int))
                              (INV_REC_g^g b$1_0 i1 (select HEAP$1 i1) b$2_0 i2 (select HEAP$2 i2) call$1_0 call$2_0 i1_res (select HEAP$1_res i1_res) i2_res (select HEAP$2_res i2_res)))
                           (let
                              ((HEAP$1 HEAP$1_res))
                              (let
                                 ((_$1_0 (select HEAP$1 b$1_0)))
                                 (let
                                    ((result$1 _$1_0)
                                     (HEAP$1_res HEAP$1)
                                     (HEAP$2 HEAP$2_res))
                                    (let
                                       ((_$2_0 (select HEAP$2 b$2_0)))
                                       (let
                                          ((result$2 _$2_0)
                                           (HEAP$2_res HEAP$2))
                                          (OUT_INV result$1 result$2 HEAP$1 HEAP$2)))))))))))))))
(assert
   (forall
      ((b$1_0_old Int)
       (HEAP$1_old (Array Int Int))
       (b$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int)
             (i2_old Int))
            (INV_REC_g^g_PRE b$1_0_old i1_old (select HEAP$1_old i1_old) b$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((b$1_0 b$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((HEAP$1 (store HEAP$1 b$1_0 1)))
               (let
                  ((result$1 0)
                   (HEAP$1_res HEAP$1)
                   (b$2_0 b$2_0_old)
                   (HEAP$2 HEAP$2_old))
                  (let
                     ((HEAP$2 (store HEAP$2 b$2_0 1)))
                     (let
                        ((result$2 0)
                         (HEAP$2_res HEAP$2))
                        (forall
                           ((i1_old Int)
                            (i2_old Int)
                            (i1_res Int)
                            (i2_res Int))
                           (INV_REC_g^g b$1_0_old i1_old (select HEAP$1_old i1_old) b$2_0_old i2_old (select HEAP$2_old i2_old) result$1 result$2 i1_res (select HEAP$1_res i1_res) i2_res (select HEAP$2_res i2_res)))))))))))
(assert
   (forall
      ((b$1_0_old Int)
       (HEAP$1_old (Array Int Int)))
      (=>
         (forall
            ((i1_old Int))
            (INV_REC_g__1_PRE b$1_0_old i1_old (select HEAP$1_old i1_old)))
         (let
            ((b$1_0 b$1_0_old)
             (HEAP$1 HEAP$1_old))
            (let
               ((HEAP$1 (store HEAP$1 b$1_0 1)))
               (let
                  ((result$1 0)
                   (HEAP$1_res HEAP$1))
                  (forall
                     ((i1_old Int)
                      (i1_res Int))
                     (INV_REC_g__1 b$1_0_old i1_old (select HEAP$1_old i1_old) result$1 i1_res (select HEAP$1_res i1_res)))))))))
(assert
   (forall
      ((b$2_0_old Int)
       (HEAP$2_old (Array Int Int)))
      (=>
         (forall
            ((i2_old Int))
            (INV_REC_g__2_PRE b$2_0_old i2_old (select HEAP$2_old i2_old)))
         (let
            ((b$2_0 b$2_0_old)
             (HEAP$2 HEAP$2_old))
            (let
               ((HEAP$2 (store HEAP$2 b$2_0 1)))
               (let
                  ((result$2 0)
                   (HEAP$2_res HEAP$2))
                  (forall
                     ((i2_old Int)
                      (i2_res Int))
                     (INV_REC_g__2 b$2_0_old i2_old (select HEAP$2_old i2_old) result$2 i2_res (select HEAP$2_res i2_res)))))))))
(check-sat)
(get-model)
