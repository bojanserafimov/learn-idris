module Main

%default total


data Even : Nat -> Type where
  ZeroEven : Even Z
  PlusTwo : Even x -> Even (S (S x))

Uninhabited (Even (S Z)) where
  uninhabited ZeroEven impossible
  uninhabited (PlusTwo _) impossible

lemma_1 : (x : Nat) -> Even (2 * x)
lemma_1 Z = ZeroEven
lemma_1 (S x) = rewrite (sym (plusSuccRightSucc x (plus x 0))) in PlusTwo (lemma_1 x)

lemma_4 : (x : Nat) -> Even (S (S x)) -> Even x
lemma_4 Z _ = ZeroEven
lemma_4 (S Z) ZeroEven impossible
lemma_4 (S Z) (PlusTwo _) impossible
lemma_4 (S (S x)) (PlusTwo even_x) = even_x

lemma_2 : (x : Nat) -> (y : Nat) -> Even x -> Even (x + y) -> Even y
lemma_2 Z y _ even_y = even_y
lemma_2 (S Z) _ _ _ impossible
lemma_2 (S (S x)) y even_x_plus_two even_sum_plus_two =
  lemma_2 x y (lemma_4 x even_x_plus_two) (lemma_4 (x + y) even_sum_plus_two)

lemma_3 : (x : Nat) -> Even (x * x) -> Even x
lemma_3 Z _ = ZeroEven
lemma_3 (S Z) prf impossible
lemma_3 (S (S x)) (PlusTwo prf) = PlusTwo $ lemma_3 x $ lemma_2 (2 * (1 + 2 * x)) (mult x x) (lemma_1 (1 + 2 * x)) (replace obvious prf)
  where
    obvious : x + (2 + (x + (x * (2 + x)))) = 2 * (1 + 2 * x) + (x * x)
    obvious = rewrite multDistributesOverPlusRight x 2 x in
              rewrite plusZeroRightNeutral x in
              rewrite plusZeroRightNeutral (x + x) in
              rewrite plusAssociative x 2 (x + ((x * 2) + (x * x))) in
              rewrite plusCommutative x 2 in
              rewrite sym (plusSuccRightSucc (x + x) (x + x)) in
              rewrite plusAssociative x (x * 2) (x * x) in
              rewrite plusAssociative x (x + (x * 2)) (x * x) in
              rewrite plusAssociative x x (x * 2) in
              rewrite multCommutative x 2 in
              rewrite plusZeroRightNeutral x in
                  Refl

half : (x : Nat) -> {auto p : Even x} -> Nat
half Z {p=ZeroEven} = Z
half (S Z) impossible
half (S (S x)) {p=(PlusTwo prf)} = S (half x)

lteAddBothRight : (x, a, b : Nat) -> LTE a b -> LTE (a + x) (b + x)
lteAddBothRight Z a b prf = rewrite plusZeroRightNeutral a in
                            rewrite plusZeroRightNeutral b in
                              prf
lteAddBothRight (S x) a b prf = rewrite sym (plusSuccRightSucc a x) in
                                rewrite sym (plusSuccRightSucc b x) in
                                  LTESucc (lteAddBothRight x a b prf)

lteEq : x = y -> LTE x y
lteEq Refl = lteRefl

lemma_5 : (x : Nat) -> {auto p : Even x} -> 2 * (half x) = x
lemma_5 Z {p=ZeroEven} = Refl
lemma_5 (S (S x)) {p=(PlusTwo prf)} =
  rewrite sym (plusSuccRightSucc (half x) (plus (half x) 0)) in
  rewrite lemma_5 x in
      Refl

lemma_12 : (x : Nat) -> {auto p : Even (S (S x))} -> LTE 1 (half (S (S x)))
lemma_12 x with (decEq (half (S (S x))) Z)
  lemma_12 x | Yes pEq = absurd $ trans (sym $ cong {f= \a => 2 * a} pEq) (lemma_5 (S (S x)))
  lemma_12 x | No pDiff with (half (S (S x)))
    lemma_12 x | No pDiff | Z = void $ pDiff Refl
    lemma_12 x | No pDiff | (S n) = LTESucc LTEZero

lemma_6 : (x : Nat) -> {auto p : Even (S x)} -> LTE (half (S x)) x
lemma_6 Z impossible
lemma_6 (S x) = let tmp = lteEq (lemma_5 (S (S x))) in
                let tmp_2 = lteAddBothRight (half (S (S x)) + 0) 1 (half (S (S x))) (lemma_12 x) in
                let tmp_3 = lteTransitive tmp_2 tmp in
                let tmp_4 = LTESucc $ lteEq $ sym $ plusZeroRightNeutral $ half $ S $ S x in
                   fromLteSucc $ lteTransitive tmp_4 tmp_3

lemma_7 : (x : Nat) -> {auto p : Even (S x)} -> (y : Nat) -> LTE ((half (S x)) + y) (x + y)
lemma_7 x y = lteAddBothRight y (half (S x)) x (lemma_6 x)

lemma_8 : (x : Nat) -> (y : Nat) -> LTE (y + x) (x + y)
lemma_8 x y = rewrite plusCommutative y x in lteRefl

lemma_9 : (x : Nat) -> (y : Nat) -> 2 * x = 2 * y -> x = y
lemma_9 Z Z Refl = Refl
lemma_9 (S x) Z Refl impossible
lemma_9 Z (S y) Refl impossible
lemma_9 (S x) (S y) equality = eqSucc x y (lemma_9 x y (tmp equality))
  where
    tmp : 2 * (S x) = 2 * (S y) -> 2 * x = 2 * y
    tmp prf =
         let t = succInjective (plus x (S (plus x 0))) (plus y (S (plus y 0))) prf in
         let t1 = plusSuccRightSucc x (plus x 0) in
         let t2 = plusSuccRightSucc y (plus y 0) in
         let t3 = trans (trans t1 t) (sym t2) in
             succInjective (plus x (plus x 0)) (plus y (plus y 0)) t3

lemma_10 : (x : Nat) -> (2 * x) * (2 * x) = 2 * (2 * x * x)
lemma_10 x = rewrite multCommutative 2 x in
             rewrite sym (multAssociative x 2 x) in
             rewrite multAssociative 2 x (2 * x) in
             rewrite multCommutative 2 x in
                 Refl

one_solution : (x : Nat) -> (y : Nat) -> (bound : Nat) -> LTE (x + y) bound -> x * x = 2 * (y * y) -> x = Z
one_solution Z _ _ _ _ = Refl
one_solution (S x) Z _ _ Refl impossible
one_solution (S x) (S y) (S tighter_bound) (LTESucc bound_prf) equality =
  let even_x = lemma_3 (S x) (replace (sym equality) (lemma_1 ((S y) * (S y)))) in
  let half_x = half (S x) in
  let two_halves = lemma_5 (S x) in
  let tighter_bound_prf = lteTransitive (lemma_8 half_x (S y)) (lteTransitive (lemma_7 x (S y)) bound_prf) in
  let two_halves_squared = cong {f=(\e => e * e)} two_halves in
  let combined = trans (sym (trans two_halves_squared equality)) (lemma_10 half_x) in
  let combined_half = lemma_9 ((S y) * (S y)) (2 * half_x * half_x) combined in
  let half_equality = trans combined_half (sym (multAssociative 2 half_x half_x)) in
  let y_is_zero = one_solution (S y) half_x tighter_bound tighter_bound_prf half_equality in
    absurd y_is_zero

irrational_sqrt_2 : (x : Nat) -> (y : Nat) -> Not (y = Z) -> x * x = 2 * (y * y) -> Void
irrational_sqrt_2 x Z nonzero_y equality = void $ nonzero_y Refl
irrational_sqrt_2 x (S y) nonzero_y equality =
  let zero_x = one_solution x (S y) (x + (S y)) lteRefl equality in
    absurd $ trans (sym equality) (cong {f=\e => e * e} zero_x)

main : IO ()
main = pure ()


