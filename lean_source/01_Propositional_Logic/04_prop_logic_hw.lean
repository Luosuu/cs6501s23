
inductive prop_var : Type
| mk (n : ℕ)

-- examples
def v₀ := prop_var.mk 0
def v₁ := prop_var.mk 1
def v₂ := prop_var.mk 2

inductive binop
| opAnd
| opOr
| opImp
| opIff
| opXor

open binop

inductive unop
| opNot

open unop

inductive prop_expr : Type
| pLit (b : bool)                         -- literal expressions
| pVar (v: prop_var)                      -- variable expressions
| pUnOp (op: unop) (e : prop_expr)        -- hw unary operator expression
| pBinOp (op : binop) (e1 e2 : prop_expr) -- binary operator expressions
-- | pNot (e : prop_expr)                    -- unary operator expression


-- original abstract syntax
-- inductive prop_expr : Type
-- | pTrue : prop_expr
-- | pFalse : prop_expr
-- | pVar (v: prop_var)
-- | pNot (e : prop_expr)
-- | pAnd (e1 e2 : prop_expr)
-- | pOr (e1 e2 : prop_expr)
-- | pImp (e1 e2 : prop_expr)
-- | pIff (e1 e2 : prop_expr)
-- | pXor (e1 e2 : prop_expr)

open prop_expr

-- An example of an "and" expression
def an_and_expr :=
  pBinOp
    opAnd                   -- binary operator
    (pVar (prop_var.mk 0))  -- variable expression
    (pVar (prop_var.mk 1))  -- variable expression

def True := pLit tt
def False := pLit ff


notation (name := pVar) `[` v `]` :=  pVar v
notation (name := pAnd) e1 ∧ e2 :=  pBinOp opAnd e1 e2
notation (name := pOr) e1 ∨ e2 :=  pBinOp opOr e1 e2
notation (name := pNot) ¬e := pUnOp opNot e
notation (name := pImp) e1 => e2 := pBinOp opImp e1 e2
notation (name := pIff) e1 ↔ e2 := pBinOp opIff e1 e2
notation (name := pXor) e1 ⊕ e2 := pBinOp opXor e1 e2
-- notation (name := pNot) ¬e := pNot e

-- first original notation
-- notation (name := var_mk) `[` v `]` :=  pVar v
-- notation (name := pAnd) e1 ∧ e2 :=  pAnd e1 e2
-- notation (name := pOr) e1 ∨ e2 :=  pOr e1 e2
-- notation (name := pNot) ¬e := pNot e
-- notation (name := pImp) e1 => e2 := pImp e1 e2
-- notation (name := pIff) e1 ↔ e2 := pIff e1 e2
-- notation (name := pXor) e1 ⊕ e2 := pXor e1 e2

def X := [v₀]
def Y := [v₁]
def Z := [v₂]

-- original variable expressions
-- def X := [prop_var.mk 0]
-- def Y := [prop_var.mk 1]
-- def Z := [prop_var.mk 2]

def e1 := X ∧ Y
def e2 := X ∨ Y
def e3 := ¬ Z
def e4 := e1 => e2  -- avoid overloading →
def e5 := e1 ↔ e1
def e6 := X ⊕ ¬X

def bimp : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := tt
| ff ff := tt

def biff : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := ff
| ff ff := tt

def op_sem : binop → (bool → bool → bool) -- operation semantics
| opAnd := band
| opOr  := bor
| opImp := bimp
| opIff := biff
| opXor := bxor

def unop_sem: unop → (bool → bool)
| opNot := bnot

#reduce ((op_sem opAnd) tt ff)
#reduce (op_sem opOr tt ff)

-- original Operational semantics
-- def pEval : prop_expr → (prop_var → bool) → bool
-- | pTrue _ := tt
-- | pFalse _ := ff
-- | ([v]) i := i v
-- | (¬ e) i := bnot (pEval e i)
-- | (e1 ∧ e2) i := (pEval e1 i) && (pEval e2 i)
-- | (e1 ∨ e2) i := (pEval e1 i) || (pEval e2 i)
-- | (e1 => e2) i := bimp (pEval e1 i) (pEval e2 i)
-- | (e1 ↔ e2) i := biff (pEval e1 i) (pEval e2 i)
-- | (e1 ⊕ e2) i := xor (pEval e1 i) (pEval e2 i)

def pEval : prop_expr → (prop_var → bool) → bool
| (pLit b)          i := b
| ([v])             i := i v                  -- our [] notation on the left
| (pUnOp unop e)    i := unop_sem unop (pEval e i)     -- our ¬ notation; Lean's bnot
--| (¬e)              i := bnot (pEval e i)     -- our ¬ notation; Lean's bnot
| (pBinOp op e1 e2) i := op_sem op (pEval e1 i) (pEval e2 i) -- hw1
-- | (pBinOp op e1 e2) i := (pEval e1 i) && (pEval e2 i) -- BUG!



