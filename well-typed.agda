module well-typed where
open import Data.Nat
open import Data.Bool using(Bool; if_then_else_; true; false)
open import Data.List
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

variable
  T : Set
  
data Exp : Set → Set where
  val : T → Exp T
  if : Exp Bool → Exp T → Exp T → Exp T
  add : Exp ℕ → Exp ℕ → Exp ℕ

eval : Exp T → T
eval (val x) = x
eval (if b x y) = if (eval b) then (eval x) else (eval y)
eval (add x y) = eval x + eval y

variable
  S S' S'' : List Set

data Stack : List Set → Set where
  ε : Stack []
  _▷_ : T → Stack S → Stack (T ∷ S)

data Code : List Set → List Set → Set₁ where
  PUSH : T → Code S (T ∷ S)
  _+++_ : Code S S' → Code S' S'' → Code S S''
  IF : Code S S' → Code S S' → Code (Bool ∷ S) S'
  ADD : Code (ℕ ∷ ℕ ∷ S) (ℕ ∷ S)

exec : Code S S' → Stack S → Stack S'
exec (PUSH x) s = x ▷ s
exec (c1 +++ c2) s = exec c2 (exec c1 s)
exec (IF c1 c2) (b ▷ s) = if b then exec c1 s else exec c2 s
exec ADD (m ▷ (n ▷ s)) = (n + m) ▷ s

compile : Exp T → Code S (T ∷ S)
compile (val x) = PUSH x
compile (if b x y) = compile b +++ IF (compile x) (compile y)
compile (add x y) = (compile x +++ compile y) +++ ADD

distrib-if : {A B : Set} (b : Bool) (x y : A) (f : A → B) → (f (if b then x else y)) ≡ (if b then f x else f y)
distrib-if false x y f = refl
distrib-if true x y f = refl
correct : (e : Exp T) (s : Stack S) → exec (compile e) s ≡ eval e ▷ s
correct (val x) s =
  begin
    exec (compile (val x)) s
  ≡⟨ refl ⟩
    (x ▷ s)
  ≡⟨ refl ⟩
    (eval (val x) ▷ s)
  ∎
correct (add x y) s =
  begin
    exec (compile (add x y)) s
  ≡⟨⟩
    exec ((compile x +++ compile y) +++ ADD) s
  ≡⟨⟩
    exec ADD (exec (compile x +++ compile y) s)
  ≡⟨⟩
    exec ADD (exec (compile y) (exec (compile x) s))
  ≡⟨ cong (λ st → exec ADD st) (correct y (exec (compile x) s)) ⟩
    exec ADD (eval y ▷ exec (compile x) s)
  ≡⟨ cong (λ st → exec ADD (eval y ▷ st)) (correct x s) ⟩
    exec ADD (eval y ▷ (eval x ▷ s))
  ≡⟨⟩
    (eval x + eval y) ▷ s
  ≡⟨⟩
    (eval (add x y) ▷ s)
  ∎
correct (if b x y) s =
  begin
    exec (compile (if b x y)) s
  ≡⟨⟩
    exec (compile b +++ IF (compile x) (compile y)) s
  ≡⟨⟩
    exec (IF (compile x) (compile y)) (exec (compile b) s)
  ≡⟨ cong (λ st → exec (IF (compile x) (compile y)) st) (correct b s) ⟩
    exec (IF (compile x) (compile y)) (eval b ▷ s)
  ≡⟨⟩
    (if eval b then exec (compile x) s else exec (compile y) s)
  ≡⟨ cong (λ st → (if eval b then st else exec (compile y) s)) (correct x s) ⟩
    (if eval b then eval x ▷ s else exec (compile y) s)
  ≡⟨ cong (λ st → (if eval b then eval x ▷ s else st)) (correct y s) ⟩
    (if eval b then eval x ▷ s else eval y ▷ s)
  ≡⟨ sym (distrib-if (eval b) (eval x) (eval y) λ x → x ▷ s) ⟩
    (if eval b then eval x else eval y) ▷ s
  ≡⟨⟩
    eval (if b x y) ▷ s
  ∎
