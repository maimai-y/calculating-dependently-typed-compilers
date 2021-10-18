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
infixr 40 _▷_

data Code : List Set → List Set → Set₁ where
  PUSH : T → Code (T ∷ S) S' → Code S S'
  IF : Code S S' → Code S S' → Code (Bool ∷ S) S'
  ADD : Code (ℕ ∷ S) S' → Code (ℕ ∷ ℕ ∷ S) S'
  HALT : Code S S

exec : Code S S' → Stack S → Stack S'
exec (PUSH x c) s = exec c (x ▷ s)
exec (IF c1 c2) (b ▷ s) = if b then exec c1 s else exec c2 s
exec (ADD c) (m ▷ n ▷ s) = exec c ((n + m) ▷ s)
exec HALT s = s

comp : Exp T → Code (T ∷ S) S' → Code S S'
comp (val x) c = PUSH x c
comp (if b x y) c = comp b (IF (comp x c) (comp y c))
comp (add x y) c = comp x (comp y (ADD c))

compile : Exp T → Code S (T ∷ S)
compile e = comp e HALT

distrib-if : {A B : Set} (b : Bool) (x y : A) (f : A → B) → (f (if b then x else y)) ≡ (if b then f x else f y)
distrib-if false x y f = refl
distrib-if true x y f = refl
correct : (e : Exp T) (s : Stack S) (c : Code (T ∷ S) S') → exec (comp e c) s ≡ exec c (eval e ▷ s)
correct (val x) s c =
  begin
    exec (comp (val x) c) s
  ≡⟨ refl ⟩
    exec (PUSH x c) s
  ≡⟨ refl ⟩
    exec c (x ▷ s)
  ≡⟨ refl ⟩
    exec c (eval (val x) ▷ s)
  ∎
correct (if b x y) s c =
  begin
    exec (comp (if b x y) c) s
  ≡⟨ refl ⟩
    exec (comp b (IF (comp x c) (comp y c))) s
  ≡⟨ correct b s (IF (comp x c) (comp y c)) ⟩
    exec (IF (comp x c) (comp y c)) (eval b ▷ s)
  ≡⟨ refl ⟩
    (if eval b then exec (comp x c) s else exec (comp y c) s)
  ≡⟨ cong (λ st → (if eval b then st else exec (comp y c) s)) (correct x s c) ⟩
    (if eval b then exec c ((eval x) ▷ s) else exec (comp y c) s)
  ≡⟨ cong (λ st → (if eval b then exec c ((eval x) ▷ s) else st)) (correct y s c) ⟩
    (if (eval b) then exec c ((eval x) ▷ s) else exec c ((eval y) ▷ s))
  ≡⟨ sym (distrib-if (eval b) ((eval x) ▷ s) ((eval y) ▷ s) λ s → exec c s) ⟩
    exec c (if (eval b) then (eval x) ▷ s else (eval y) ▷ s)
  ≡⟨ cong (λ s -> exec c s) (sym (distrib-if (eval b) (eval x) (eval y) λ v → v ▷ s)) ⟩
    exec c ((if (eval b) then (eval x) else (eval y)) ▷ s)
  ≡⟨ refl ⟩
    exec c (eval (if b x y) ▷ s)
  ∎
correct (add x y) s c =
  begin
    exec (comp (add x y) c) s
  ≡⟨ refl ⟩
    exec (comp x (comp y (ADD c))) s
  ≡⟨ correct x s (comp y (ADD c)) ⟩
    exec (comp y (ADD c)) (eval x ▷ s)
  ≡⟨ correct y (eval x ▷ s) (ADD c) ⟩
    exec (ADD c) (eval y ▷ eval x ▷ s)
  ≡⟨ refl ⟩
    exec c ((eval x + eval y) ▷ s)
  ≡⟨ refl ⟩
    exec c (eval (add x y) ▷ s)
  ∎

correct' : (e : Exp T) (s : Stack S) → exec (comp e HALT) s ≡ eval e ▷ s
correct' e s =
  begin
    exec (comp e HALT) s
  ≡⟨ correct e s HALT ⟩
    exec HALT (eval e ▷ s)
  ≡⟨ refl ⟩
    eval e ▷ s
  ∎
