module well-typed-exception where
open import Data.Nat
open import Data.Bool using(Bool; if_then_else_; true; false; _∨_; _∧_)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

variable
  a b : Bool

data Exp : Bool → Set where
  val : ℕ → Exp false
  add : Exp a → Exp b → Exp (a ∨ b)
  throw : Exp true
  catch : Exp a → Exp b → Exp (a ∧ b)

eval? : Exp b → Maybe ℕ
eval? (val n) = just n
eval? (add x y) with eval? x
... | nothing = nothing
... | just n with eval? y
... | nothing = nothing
... | just m = just (n + m)
eval? throw = nothing
eval? (catch x h) with eval? x
... | nothing = eval? h
... | just n = just n

eval : b ≡ false → Exp b → ℕ
eval p (val n) = n
eval p (add {false} {false} x y) = eval refl x + eval refl y
eval p (catch {false} {a} x h) = eval refl x
eval p (catch {true} {false} x h) with eval? x
... | nothing = eval refl h
... | just n = n
       
data Ty : Set where
  nat : Ty
  han : List Ty → List Ty → Ty

variable
  T : Ty

variable
  S S' S'' : List Ty

El : Ty → Set
data Code : List Ty → List Ty → Set

El nat = ℕ
El (han S S') = Code S S'

data Code where
  PUSH : El T → Code (T ∷ S) S' → Code S S'
  ADD : Code (nat ∷ S) S' → Code (nat ∷ nat ∷ S) S'
  UNMARK : Code (T ∷ S) S' → Code (T ∷ han S S' ∷ S) S'
  MARK : Code S S' → Code (han S S' ∷ S) S' → Code S S'
  THROW : Code (S'' ++ han S S' ∷ S) S'
  HALT : Code S S

data Stack : List Ty → Set where
  ϵ : Stack []
  _▷_ : El T → Stack S → Stack (T ∷ S)
infixr 40 _▷_

{-# TERMINATING #-}
fail : Stack (S'' ++ han S S' ∷ S) → Stack S'
exec : Code S S' → Stack S → Stack S'

fail {[]} (h' ▷ s) = exec h' s
fail {_ ∷ _} (n ▷ s) = fail s

exec (PUSH x c) s = exec c (x ▷ s)
exec (ADD c) (m ▷ n ▷ s) = exec c ((n + m) ▷ s)
exec (UNMARK c) (x ▷ h ▷ s) = exec c (x ▷ s)
exec (MARK h c) s = exec c (h ▷ s)
exec THROW s = fail s
exec HALT s = s

comp? : Exp b → Code (nat ∷ (S'' ++  han S S' ∷ S)) S' → Code (S'' ++  han S S' ∷ S) S'

comp : b ≡ false → Exp b → Code (nat ∷ S) S' → Code S S'
comp p (val x) c = PUSH x c
comp p (add {false} {false} x y) c = (comp refl x (comp refl y (ADD c)))
comp p (catch {false} {_} x h) c = comp refl x c
comp p (catch {true} {false} x h) c = MARK (comp refl h c) (comp? {S'' = []} x (UNMARK c))

correct?-just :
  {n : ℕ}
  (e : Exp b)
  (s : Stack (S'' ++ han S S' ∷ S))
  (c : Code (nat ∷ (S'' ++ han S S' ∷ S)) S')
  (option : eval? e ≡ (just n)) →
  exec (comp? e c) s ≡ exec c (n ▷ s)
  
correct?-nothing :
  (e : Exp b)
  (s : Stack (S'' ++ han S S' ∷ S))
  (c : Code (nat ∷ (S'' ++ han S S' ∷ S)) S')
  (option : eval? e ≡ nothing) →
  exec (comp? e c) s ≡ fail s
       
correct : (p : b ≡ false) (e : Exp b) (s : Stack S) (c : Code (nat ∷ S) S') → exec (comp p e c) s ≡ exec c (eval p e ▷ s)
       
correct p (val x) s c =
  begin
    exec (comp p (val x) c) s
  ≡⟨ refl ⟩
    exec (PUSH x c) s
  ≡⟨ refl ⟩
    exec c (x ▷ s)
  ≡⟨ refl ⟩
    exec c (eval p (val x) ▷ s)
  ∎

correct p (add {false} {false} x y) s c =
  begin
    exec (comp p (add {false} {false} x y) c) s
  ≡⟨ refl ⟩
    exec (comp refl x (comp refl y (ADD c))) s
  ≡⟨ correct refl x s (comp refl y (ADD c)) ⟩
    exec (comp refl y (ADD c)) (eval refl x ▷ s)
  ≡⟨ correct refl y (eval refl x ▷ s) (ADD c) ⟩
    exec (ADD c) (eval refl y ▷ eval refl x ▷ s)
  ≡⟨ refl ⟩
    exec c (((eval refl x) + (eval refl y)) ▷ s)
  ≡⟨ refl ⟩
    exec c (eval p (add {false} {false} x y) ▷ s)
  ∎
  
correct p (catch {false} {_} x h) s c =
  begin
    exec (comp p (catch {false} {_} x h) c) s
  ≡⟨ refl ⟩
    exec (comp refl x c) s
  ≡⟨ correct refl x s c ⟩
    exec c (eval refl x ▷ s)
  ≡⟨ refl ⟩
    exec c (eval p (catch {false} {_} x h) ▷ s)
  ∎

correct p (catch {true} {false} x h) s c with eval? x | inspect eval? x
correct p (catch {true} {false} x h) s c    | nothing | Relation.Binary.PropositionalEquality.[ eq ] =
  begin
    exec (comp p (catch {true} {false} x h) c) s
  ≡⟨ refl ⟩
    exec (MARK (comp refl h c) (comp? {S'' = []} x (UNMARK c))) s
  ≡⟨ refl ⟩
    exec (comp? {S'' = []} x (UNMARK c)) (comp refl h c ▷ s)
  ≡⟨ correct?-nothing {S'' = []} x (comp refl h c ▷ s) (UNMARK c) eq ⟩
    fail {S'' = []} (comp refl h c ▷ s)
  ≡⟨ refl ⟩
    exec (comp refl h c) s
  ≡⟨ correct refl h s c ⟩
    exec c (eval refl h ▷ s)
  ∎
correct p (catch {true} {false} x h) s c | just n | Relation.Binary.PropositionalEquality.[ eq ] =
  begin
    exec (comp p (catch {true} {false} x h) c) s
  ≡⟨ refl ⟩
    exec (MARK (comp refl h c) (comp? {S'' = []} x (UNMARK c))) s
  ≡⟨ refl ⟩
    exec (comp? {S'' = []} x (UNMARK c)) (comp refl h c ▷ s)
  ≡⟨ correct?-just {S'' = []} x (comp refl h c ▷ s) (UNMARK c) eq ⟩
    exec (UNMARK c) (n ▷ comp refl h c ▷ s)
  ≡⟨ refl ⟩
    exec c (n ▷ s)
  ∎

comp? (val x) c = PUSH x c
comp? (add x y) c = comp? x (comp? {S'' = nat ∷ _} y (ADD c))
comp? throw c = THROW
comp? (catch x h) c = MARK (comp? h c) (comp? {S'' = []} x (UNMARK c))

correct?-just (val x) s c refl =
  begin
    exec (comp? (val x) c) s
  ≡⟨ refl ⟩
    exec (PUSH x c) s
  ≡⟨ refl ⟩
    exec c (x ▷ s)
  ∎

correct?-just (add x y) s c p with eval? x | inspect eval? x
... | just n | p with eval? y | inspect eval? y
correct?-just (add x y) s c refl | just n | Relation.Binary.PropositionalEquality.[ eq-x ] | just m | Relation.Binary.PropositionalEquality.[ eq-y ] =
  begin
    exec (comp? (add x y) c) s
  ≡⟨ refl ⟩
    exec (comp? x (comp? {S'' = nat ∷ _} y (ADD c))) s
  ≡⟨ correct?-just x s (comp? {S'' = nat ∷ _} y (ADD c)) eq-x ⟩
    exec (comp? {S'' = nat ∷ _} y (ADD c)) (n ▷ s)  
  ≡⟨ correct?-just y (n ▷ s) (ADD c) eq-y ⟩
    exec (ADD c) (m ▷ n ▷ s)
  ≡⟨ refl ⟩
    exec c ((n + m) ▷ s)
  ∎
  
correct?-just (catch x h) s c p with eval? x | inspect eval? x
correct?-just (catch x h) s c refl | just n | Relation.Binary.PropositionalEquality.[ eq-x ] =
  begin
    exec (comp? (catch x h) c) s
  ≡⟨ refl ⟩
    exec (MARK (comp? h c) (comp? {S'' = []} x (UNMARK c))) s
  ≡⟨ refl ⟩
    exec (comp? {S'' = []} x (UNMARK c)) (comp? h c ▷ s)
  ≡⟨ correct?-just x (comp? h c ▷ s) (UNMARK c) eq-x ⟩
    exec (UNMARK c) (n ▷ comp? h c ▷ s)
  ≡⟨ refl ⟩
    exec c (n ▷ s)
  ∎
... | nothing | eq with eval? h | inspect eval? h
correct?-just (catch x h) s c refl | nothing | Relation.Binary.PropositionalEquality.[ eq-x ] | just n | Relation.Binary.PropositionalEquality.[ eq-h ] =
  begin
    exec (comp? (catch x h) c) s
  ≡⟨ refl ⟩
    exec (MARK (comp? h c) (comp? {S'' = []} x (UNMARK c))) s
  ≡⟨ refl ⟩
    exec (comp? {S'' = []} x (UNMARK c)) (comp? h c ▷ s)
  ≡⟨ correct?-nothing {S'' = []} x (comp? h c ▷ s) (UNMARK c) eq-x ⟩
    fail {S'' = []} (comp? h c ▷ s)
  ≡⟨ refl ⟩
    exec (comp? h c) s
  ≡⟨ correct?-just h s c eq-h ⟩
    exec c (n ▷ s)
  ∎

correct?-nothing (add x y) s c p with eval? x | inspect eval? x
... | nothing | Relation.Binary.PropositionalEquality.[ eq-x ] =
  begin
    exec (comp? x (comp? {S'' = nat ∷ _} y (ADD c))) s
  ≡⟨ correct?-nothing x s (comp? {S'' = nat ∷ _} y (ADD c)) eq-x ⟩
    fail s
  ∎
... | just n | p with eval? y | inspect eval? y
correct?-nothing (add x y) s c p | just n | Relation.Binary.PropositionalEquality.[ eq-x ] | nothing | Relation.Binary.PropositionalEquality.[ eq-y ] =
  begin
    exec (comp? x (comp? {S'' = nat ∷ _} y (ADD c))) s
  ≡⟨ correct?-just x s (comp? {S'' = nat ∷ _} y (ADD c)) eq-x ⟩
    exec (comp? {S'' = nat ∷ _} y (ADD c)) (n ▷ s)
  ≡⟨ correct?-nothing y (n ▷ s) (ADD c) eq-y ⟩
    fail s
  ∎

correct?-nothing throw s c p =
  begin
    exec (comp? throw c) s
  ≡⟨ refl ⟩
    exec THROW s
  ≡⟨ refl ⟩
    fail s
  ∎

correct?-nothing (catch x h) s c p with eval? x | inspect eval? x
... | nothing | eq with eval? h | inspect eval? h
correct?-nothing (catch x h) s c p | nothing | Relation.Binary.PropositionalEquality.[ eq-x ] | nothing | Relation.Binary.PropositionalEquality.[ eq-h ] =
  begin
    exec (comp? (catch x h) c) s
  ≡⟨ refl ⟩
    exec (MARK (comp? h c) (comp? {S'' = []} x (UNMARK c))) s
  ≡⟨ refl ⟩
    exec (comp? {S'' = []} x (UNMARK c)) (comp? h c ▷ s)
  ≡⟨ correct?-nothing x (comp? h c ▷ s) (UNMARK c) eq-x ⟩
    fail {S'' = []} (comp? h c ▷ s)
  ≡⟨ refl ⟩
    exec (comp? h c) s
  ≡⟨ correct?-nothing h s c eq-h ⟩
    fail s
  ∎

compile : b ≡ false → Exp b → Code S (nat ∷ S)
compile p e = comp p e HALT

correct' : (p : b ≡ false) (e : Exp b) (s : Stack S) → exec (compile p e) s ≡ eval p e ▷ s
correct' p e s =
  begin
    exec (compile p e) s
  ≡⟨ refl ⟩
    exec (comp p e HALT) s
  ≡⟨ correct p e s HALT ⟩
    exec HALT (eval p e ▷ s)
  ≡⟨ refl ⟩
    eval p e ▷ s
  ∎
