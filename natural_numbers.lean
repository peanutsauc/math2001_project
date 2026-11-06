inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ
  deriving DecidableEq, Repr


namespace ℕ
protected def ofNat : Nat → ℕ
  | 0          => .zero
  | Nat.succ n => .succ (ℕ.ofNat n)

@[default_instance 200]
instance (n : Nat) : OfNat ℕ n where
  ofNat := ℕ.ofNat n
end ℕ


def plus : ℕ → ℕ → ℕ 
  | ℕ.zero, n => n
  | ℕ.succ m, n => ℕ.succ ( plus m n )

def times : ℕ → ℕ → ℕ 
  | ℕ.zero, _ => ℕ.zero
  | ℕ.succ m, n => plus n ( times m n )
  
def power : ℕ → ℕ → ℕ
  | _, ℕ.zero => 1
  | n, ℕ.succ m => times n ( power n m ) 

macro_rules
| `($m + $n) => `(plus $m $n)
| `($m * $n) => `(times $m $n)
| `($n ^ $m) => `(power $n $m)



@[app_unexpander plus]
meta def unexpandPlus : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a + $b)
  | _ => throw ()

@[app_unexpander times]
meta def unexpandTimes : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a * $b)
  | _ => throw ()


def le ( m n : ℕ ) : Prop :=
  ∃ (k:ℕ), k + m = n



def lt ( m n : ℕ ) : Prop :=
  ( le m n ) ∧ ¬ ( m = n )

macro_rules
| `($m ≤ $n) => `(le $m $n)
| `($m < $n) => `(lt $m $n)
| `($m ≥ $n) => `(le $n $m)
| `($m > $n) => `(lt $n $m)

@[app_unexpander le]
meta def unexpandLe : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a ≤ $b)
  | _ => throw ()

@[app_unexpander lt]
meta def unexpandLt : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a < $b)
  | _ => throw ()

-- def «ℕ₊» := { n : ℕ // n > 0 }


def divides (m n : ℕ) : Prop :=
  ∃ (k:ℕ), k*m = n


/- Intervals -/

def InitialSegment (m:ℕ) := { n : ℕ // n ≤  m }
def FinalSegment (m:ℕ) := { n : ℕ // n ≥ m }

structure ℕ.Interval where
  lower : ℕ
  upper : ℕ

instance : CoeSort ℕ.Interval Type where
  coe I := { n : ℕ // I.lower ≤ n ∧ n ≤ I.upper }

notation "ℕ≤" m => InitialSegment m
notation "ℕ≥" m => FinalSegment m
notation "ℕ₊" => ℕ> 0

macro_rules
| `(ℕ[$a $b]) => `(ℕ.Interval.mk $a $b)


/- Remainder -/

def remainder : ℕ → ℕ → ℕ
| 0, _ => 0
| ℕ.succ n, m => 
  let r := (remainder n m).succ
  if r = m then 0 else r

macro_rules
| `($n % $m) => `(remainder $n $m)

@[app_unexpander remainder]
meta def unexpandRemainder : Lean.PrettyPrinter.Unexpander
  | `($_ $n $m) => `($n % $m)
  | _ => throw ()

    
 /- Sums and products -/ 

def sum ( f : ℕ → ℕ )  : ℕ → ℕ
| 0 => 0
| ℕ.succ M => ( sum f M ) + f M.succ

def prod ( f : ℕ → ℕ )  : ℕ → ℕ
| 0 => 1
| ℕ.succ M => ( prod f M ) * f M.succ



def irreducible ( n : ℕ ) : Prop :=
  (n ≠ 1) ∧ ∀ (a b : ℕ), a * b = n → a = 1 ∨ b = 1




def ℕ_pos := { n : ℕ // n > 0 }

