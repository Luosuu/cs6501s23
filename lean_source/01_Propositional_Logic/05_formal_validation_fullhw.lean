namespace cs6501

-- variables, indexed by natural numbers
inductive prop_var : Type
| mk (n : ℕ)

-- Abstract syntactic terms for unary operators
inductive unop
| opNot

-- Abstract syntactic terms for binary operators
inductive binop
| opAnd
| opOr
| opImp
| opIff
| opXor

-- make constructor names globally visible
open unop
open binop

-- syntax
inductive prop_expr : Type
| pLit (b : bool)                         -- literal expressions
| pVar (v: prop_var)                      -- variable expressions
-- | pNot (e : prop_expr)                    -- unary operator expression
| pUnOp (op :unop) (e : prop_expr)                    -- unary operator expression
| pBinOp (op : binop) (e1 e2 : prop_expr) -- binary operator expressions

open prop_expr

-- notations (concrete syntax)
def True := pLit tt
def False := pLit ff
notation (name := pVar) `[` v `]` :=  pVar v
notation (name := pNot) ¬e := pUnOp opNot e
notation (name := pAnd) e1 ∧ e2 :=  pBinOp opAnd e1 e2
notation (name := pOr) e1 ∨ e2 :=  pBinOp opOr e1 e2
precedence ` => `: 50                                      -- add operator precedence
notation (name := pImp) e1 `=>` e2 := pBinOp opImp e1 e2
notation (name := pIff) e1 ↔ e2 := pBinOp opIff e1 e2
notation (name := pXor) e1 ⊕ e2 := pBinOp opXor e1 e2
-- Let's not bother with notations for nand and nor at this point

-- Boolean implication operation
def bimp : bool → bool → bool
| tt tt := tt
| tt ff := tt
| ff tt := ff
| ff ff := tt

-- Boolean biimplication operation
def biff : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := ff
| ff ff := tt

-- interpretations of binary operators
def bin_op_sem : binop → (bool → bool → bool)
| opAnd := band
| opOr  := bor
| opImp := bimp
| opIff := biff
| opXor := bxor

-- interpretations of unary operators
def un_op_sem : unop → (bool → bool)
| opNot := bnot

-- semantic evaluation (meaning of expressions)
def pEval : prop_expr → (prop_var → bool) → bool
| (pLit b)          i := b
| ([v])             i := i v                  -- our [] notation on the left
| (pUnOp op e)      i := (un_op_sem op) (pEval e i)     -- our ¬ notation; Lean's bnot
| (pBinOp op e1 e2) i := (bin_op_sem op) (pEval e1 i) (pEval e2 i) -- BUG FIXED :-)!

-- proof of one key property: "commutativity of ∧" in the logic we've specified,, as required
theorem and_commutes :
  ∀ (e1 e2 : prop_expr)
    (i : prop_var → bool),
    (pEval (e1 ∧ e2) i) = (pEval (e2 ∧ e1) i) :=
begin
-- assume that e1 e2 and i are arbitrary
assume e1 e2 i,

-- unfold definition of pEval for given arguments
unfold pEval,

-- unfold definition of bin_op_sem
unfold bin_op_sem,

-- case analysis on Boolean value (pEval e1 i)
cases (pEval e1 i),

-- within first case, nested case analysis on (pEval e2 i)
cases (pEval e2 i),

-- goal proved by reflexivity of equality
apply rfl,

-- second case for (pEval e2 i) within first case for  (pEval e1 i)
apply rfl,

-- onto second case for (pEval e1 i)
-- again nested case analysis on (pEval e2 i)
cases (pEval e2 i),

-- and both cases are again true by reflexivity of equality
apply rfl,
apply rfl,

-- QED
end

theorem or_commutes :
  ∀ (e1 e2 : prop_expr)
    (i : prop_var → bool),
    (pEval (e1 ∨ e2) i) = (pEval (e2 ∨ e1) i) :=
begin
-- assume that e1 e2 and i are arbitrary
assume e1 e2 i,

-- unfold definition of pEval for given arguments
unfold pEval,

-- unfold definition of bin_op_sem
unfold bin_op_sem,

-- case analysis on Boolean value (pEval e1 i)
cases (pEval e1 i),

-- within first case, nested case analysis on (pEval e2 i)
cases (pEval e2 i),

-- goal proved by reflexivity of equality
apply rfl,

-- second case for (pEval e2 i) within first case for  (pEval e1 i)
apply rfl,

-- onto second case for (pEval e1 i)
-- again nested case analysis on (pEval e2 i)
cases (pEval e2 i),

-- and both cases are again true by reflexivity of equality
apply rfl,
apply rfl,

-- QED
end

theorem not_involutive :
∀ (e: prop_expr)
  (i : prop_var → bool),
  (pEval (e) i) = (pEval (¬¬e) i) :=

begin
assume e i,
unfold pEval,
unfold un_op_sem,
cases (pEval e i),
apply rfl,
apply rfl,
end

-- tell Lean to explain given notations
#print notation ¬
#print notation ∧
#print notation ↑

-- variables
def v₀ := prop_var.mk 0
def v₁ := prop_var.mk 1
def v₂ := prop_var.mk 2

-- variable expressions
def X := [v₀]
def Y := [v₁]
def Z := [v₂]

-- operator expressions
def e1 := X ∧ Y
def e2 := X ∨ Y
def e3 := ¬Z
def e4 := e1 => e2
def e5 := e1 ↔ e1
def e6 := X ⊕ ¬X

-- an interpretation
def an_interp : prop_var → bool
| (prop_var.mk 0) := tt -- X
| (prop_var.mk 1) := ff -- Y
| (prop_var.mk 2) := tt -- Z
| _ := ff               -- any other variable

-- evaluation
#reduce pEval X an_interp  -- expect false
#reduce pEval Y an_interp  -- expect false
#reduce pEval e1 an_interp  -- expect false

-- applying theorem!
#reduce and_commutes X Y an_interp
-- result is a proof that ff = ff
#reduce or_commutes X Y an_interp
-- result is a proof that tt = tt

-- implication is transitive
theorem imp_trans :
  ∀ (e1 e2 e3 : prop_expr) (i : prop_var → bool),
    (pEval (e1 => e2) i) = tt →
    (pEval (e2 => e3) i) = tt →
    (pEval (e1 => e3) i) = tt :=
begin
unfold pEval,
unfold bin_op_sem,
assume e1 e2 e3 i h12 h23,
cases (pEval e1 i),
cases (pEval e2 i),
cases (pEval e3 i),
-- first 4 cases for e1
assumption, --"exact rfl" will also work
assumption,
cases (pEval e3 i),
assumption,
assumption,
-- second four cases for e1
cases (pEval e2 i),
cases (pEval e3 i),
assumption,
assumption,
cases (pEval e3 i),
assumption,
assumption,
end

-- contrapositive: (X => Y) → (¬Y => ¬X)
theorem contrapos :
∀ (e1 e2 : prop_expr)
  (i : prop_var → bool),
  (pEval (e1 => e2) i) = tt →
  (pEval (¬e2 => ¬e1)) i = tt :=
begin
assume e1 e2 i,
unfold pEval,
unfold un_op_sem bin_op_sem,
cases (pEval e1 i),
cases (pEval e2 i),
unfold bnot bimp,
assume h,
assumption,
unfold bnot bimp,
assume h,
assumption,
cases (pEval e2 i),
unfold bnot bimp,
assume h,
assumption,
unfold bnot bimp,
assume h,
assumption,
end

theorem and_introduction:
∀ (e1 e2: prop_expr)
  (i: prop_var → bool),
  (pEval (e1 ∧ e2) i) = tt →  
  (pEval (e1 ∧ e2) i) = tt :=
begin
assume e1 e2 i,
unfold pEval,
unfold bin_op_sem,
cases pEval e1 i,
cases pEval e2 i,
assume h,
assumption,
assume h,
assumption,
cases pEval e2 i,
assume h,
assumption,
assume h,
assumption
end

theorem and_elimination_left:
∀ (e1 e2: prop_expr)
  (i: prop_var → bool),
  (pEval (e1 ∧ e2) i) = tt → 
  (pEval e1 i) = tt :=
begin
assume e1 e2 i,
unfold pEval,
unfold bin_op_sem,
cases pEval e1 i,
cases pEval e2 i,
assume h,
assumption,
assume h,
assumption,
cases pEval e2 i,
assume h,
apply rfl,
assume h,
apply rfl
end

theorem and_elimination_right:
∀ (e1 e2: prop_expr)
  (i: prop_var → bool),
  (pEval (e1 ∧ e2) i) = tt → 
  (pEval e2 i) = tt :=
begin
assume e1 e2 i,
unfold pEval,
unfold bin_op_sem,
cases pEval e1 i,
assume h,
cases pEval e2 i,
assumption,
apply rfl,
cases pEval e2 i,
assume h,
assumption,
assume h,
assumption
end


theorem negation_elimination:
∀ (e: prop_expr)
  (i: prop_var → bool),
  (pEval (¬¬e) i) = tt → 
  (pEval e i) = tt :=
begin
assume e i,
unfold pEval,
unfold un_op_sem,
cases pEval e i,
assume h,
assumption,
assume h,
apply rfl,
end

theorem no_contradiction:
∀ (e: prop_expr)
  (i: prop_var → bool),
  (pEval (¬(¬e∧e)) i) = tt :=
begin
assume e i,
unfold pEval,
unfold un_op_sem,
unfold bin_op_sem,
cases pEval e i,
apply rfl,
apply rfl,
end

theorem or_introduction_left:
∀ (e1 e2: prop_expr)
  (i: prop_var → bool),
  (pEval e1 i) = tt →
  (pEval (e1∨e2) i) = tt:=
begin
assume e1 e2 i,
unfold pEval,
unfold bin_op_sem,
cases pEval e1 i,
cases pEval e2 i,
assume h,
assumption,
assume h,
apply rfl,
cases pEval e2 i,
assume h,
apply rfl,
assume h,
apply rfl
end

theorem or_introduction_right:
∀ (e1 e2: prop_expr)
  (i: prop_var → bool),
  (pEval e2 i) = tt →
  (pEval (e1∨e2) i) = tt:=
begin
assume e1 e2 i,
unfold pEval,
unfold bin_op_sem,
cases pEval e1 i,
cases pEval e2 i,
assume h,
assumption,
assume h,
apply rfl,
cases pEval e2 i,
assume h,
apply rfl,
assume h,
apply rfl
end

-- failed
-- theorem or_elimination:
-- ∀ (e1 e2 e3: prop_expr)
--   (i: prop_var → bool),
--   (pEval ((e1∨e2)∧(e1=>e3)∧(e2=>e3)) i) = tt →
--   (pEval e3 i) = tt:=
-- begin
-- assume e1 e2 e3 i,
-- unfold pEval,
-- unfold bin_op_sem,
-- cases pEval e1 i,
-- cases pEval e2 i,
-- cases pEval e3 i,
-- unfold bimp,
-- assume h,
-- assumption,
-- unfold bimp,
-- assume h,
-- apply rfl,
-- cases pEval e3 i,
-- unfold bimp,
-- assume h,
-- assumption,
-- end


theorem iff_introduction:
∀ (e1 e2: prop_expr)
  (i: prop_var → bool),
  (pEval ((e1=>e2)∧(e2=>e1) ) i) = tt →
  (pEval (e1↔e2) i) = tt:=
begin
assume e1 e2 i,
unfold pEval,
unfold bin_op_sem,
cases pEval e1 i,
cases pEval e2 i,
unfold bimp biff,
assume h,
apply rfl,
unfold bimp biff,
assume h,
assumption,
cases pEval e2 i,
unfold bimp biff,
assume h,
assumption,
assume h,
assumption,
end


theorem iff_elimination_left:
∀ (e1 e2: prop_expr)
  (i: prop_var → bool),
  (pEval (e1↔e2) i) = tt →
  (pEval (e1=>e2) i) = tt:=
begin
assume e1 e2 i,
unfold pEval,
unfold bin_op_sem,
cases pEval e1 i,
cases pEval e2 i,
unfold bimp biff,
assume h,
apply rfl,
unfold bimp biff,
assume h,
assumption,
cases pEval e2 i,
unfold bimp biff,
assume h,
apply rfl,
assume h,
assumption,
end

theorem iff_elimination_right:
∀ (e1 e2: prop_expr)
  (i: prop_var → bool),
  (pEval (e1↔e2) i) = tt →
  (pEval (e2=>e1) i) = tt:=
begin
assume e1 e2 i,
unfold pEval,
unfold bin_op_sem,
cases pEval e1 i,
cases pEval e2 i,
unfold bimp biff,
assume h,
apply rfl,
unfold bimp biff,
assume h,
apply rfl,
cases pEval e2 i,
unfold bimp biff,
assume h,
assumption,
assume h,
assumption,
end

-- failed
-- theorem arrow_elimination:
-- ∀ (e1 e2: prop_expr)
--   (i: prop_var → bool),
--   (pEval ((e1=>e2)∧e1) i) = tt →
--   (pEval e2 i) = tt:=
-- begin
-- assume e1 e2 i,
-- unfold pEval,
-- unfold bin_op_sem,
-- cases pEval e1 i,
-- cases pEval e2 i,
-- unfold bimp,
-- assume h,
-- assumption,
-- unfold bimp,
-- assume h,
-- apply rfl,
-- cases pEval e2 i,
-- unfold bimp,
-- assume h,
-- assumption,
-- end

theorem transitivity_of_arrow:
∀ (e1 e2 e3: prop_expr)
  (i: prop_var → bool),
  (pEval ((e1=>e2)∧(e2=>e3)) i) = tt →
  (pEval (e1=>e3) i) = tt:=
begin
assume e1 e2 e3 i,
unfold pEval,
unfold bin_op_sem,
cases pEval e1 i,
cases pEval e2 i,
cases pEval e3 i,
unfold bimp,
assume h,
apply rfl,
unfold bimp,
assume h,
assumption,
unfold bimp,
cases pEval e3 i,
unfold bimp,
assume h,
apply rfl,
unfold bimp,
assume h,
assumption,
cases pEval e2 i,
cases pEval e3 i,
unfold bimp,
assume h,
apply rfl,
unfold bimp,
assume h,
apply rfl,
cases pEval e3 i,
unfold bimp,
assume h,
apply rfl,
unfold bimp,
assume h,
apply rfl
end
theorem contrapositive:
∀ (e1 e2: prop_expr)
  (i: prop_var → bool),
  (pEval (e1=>e2) i) = tt →
  (pEval (¬e2=>¬e1) i) = tt:=
begin
assume e1 e2 i,
unfold pEval,
unfold bin_op_sem,
unfold un_op_sem,
cases pEval e1 i,
cases pEval e2 i,
unfold bimp,
assume h,
apply rfl,
unfold bimp,
assume h,
assumption,
cases pEval e2 i,
unfold bimp,
assume h,
apply rfl,
unfold bimp,
assume h,
apply rfl
end

theorem DeMorgan_1:
∀ (e1 e2: prop_expr)
  (i: prop_var → bool),
  (pEval ((¬(e1∨e2))↔(¬e1∧¬e2)) i) = tt:=
begin
assume e1 e2 i,
unfold pEval,
unfold un_op_sem,
unfold bin_op_sem,
cases pEval e1 i,
cases pEval e2 i,
unfold biff bnot,
apply rfl,
apply rfl,
cases pEval e2 i,
apply rfl,
apply rfl,
end

theorem DeMorgan_2:
∀ (e1 e2: prop_expr)
  (i: prop_var → bool),
  (pEval ((¬(e1∧ e2))↔(¬e1∨¬e2)) i) = tt:=
begin
assume e1 e2 i,
unfold pEval,
unfold un_op_sem,
unfold bin_op_sem,
cases pEval e1 i,
cases pEval e2 i,
unfold biff bnot,
apply rfl,
apply rfl,
cases pEval e2 i,
apply rfl,
apply rfl,
end

end cs6501