/-
Tianle Zhong (computing id: fad3ew)
In collaboration with Mr. Archit Uniyal (deu9yh)
-/
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
| opNand
| opNor

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
-- notation (name := pNot) ¬e := pNot e
notation (name := pImp) e1 => e2 := pBinOp opImp e1 e2
notation (name := pIff) e1 ↔ e2 := pBinOp opIff e1 e2
notation (name := pXor) e1 ⊕ e2 := pBinOp opXor e1 e2
notation (name := pNand) e1 ↑ e2 := pBinOp opNand e1 e2 -- nand
notation (name := pNor) e1 × e2 := pBinOp opNor e1 e2

-- notation (name := pNor) e1 ↓ e2 := pBinOp opNor e1 e2 (error: ↓ unexpected token)

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
#check X
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
def e7 := X ↑ Y
def e8 := X × Y
def e9 := X × Z 

#reduce e7
#reduce e8
#check e1

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

def bnad: bool → bool → bool
| tt tt := ff
| tt ff := ff
| ff tt := ff
| ff ff := tt

def bnor: bool → bool → bool
| tt tt := ff
| tt ff := tt
| ff tt := tt
| ff ff := tt

def op_sem : binop → (bool → bool → bool) -- operation semantics
| opAnd := band
| opOr  := bor
| opImp := bimp
| opIff := biff
| opXor := bxor
| opNand := bnad
| opNor := bnor

def unop_sem: unop → (bool → bool)
| opNot := bnot

#reduce ((op_sem opAnd) tt ff)
#reduce (op_sem opOr tt ff)
#reduce op_sem opNand tt ff
#reduce op_sem opNor tt tt

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
| ([v])             i := i v                            -- our [] notation on the left
| (pUnOp unop e)    i := unop_sem unop (pEval e i)    -- our ¬ notation; Lean's bnot
--| (¬e)            i := bnot (pEval e i)             -- our ¬ notation; Lean's bnot
| (pBinOp op e1 e2) i := op_sem op (pEval e1 i) (pEval e2 i) -- hw1
-- | (pBinOp op e1 e2) i := (pEval e1 i) && (pEval e2 i) -- BUG!

def all_true : prop_var → bool
| _ := tt

def all_false : prop_var → bool
| _ := ff

def mixed: prop_var → bool
| (prop_var.mk 0) := tt
| (prop_var.mk 1) := ff
| (prop_var.mk 2) := tt
| (prop_var.mk _) := ff

def e_not := ¬e1
#reduce pEval e_not all_false
def e_Nand := e1 ↑ e2
#reduce pEval e_Nand all_true
def e_Nor := e1 × e2
#reduce pEval e_Nor mixed
def e_complex := (e1∧e2)×(e3=>e4)∨(e5↑e6)
#reduce pEval e_complex mixed 

#reduce mixed v₁
#reduce pEval (X ↑ Y) all_false 
#reduce pEval (X × Y) all_true
#reduce pEval (X × Y) mixed
#reduce pEval ¬(X × Y)
#reduce pEval True
#reduce pEval ¬True
#reduce pEval ((X×Y)↑(X∧Y)) all_false
#reduce pEval ((e1×e2)↑(e1∧e2)) all_false
#reduce pEval ((e1×e2)↑(e1∧e2)) mixed
