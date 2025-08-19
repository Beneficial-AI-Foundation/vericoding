//ATOM

// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

//IMPL 

/* code modified by LLM (iteration 2): added helper lemma for exponentiation multiplication */
lemma ExpMultiplicationProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  reveal Exp_int;
  if a == 0 {
    // base case: Exp_int(x, 0 + b) == 1 * Exp_int(x, b)
  } else {
    // inductive case
    ExpMultiplicationProperty(x, a-1, b);
  }
}

/* code modified by LLM (iteration 2): added helper lemma for power of 2 relationship */
lemma PowerOf2Property(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n-1)
{
  reveal Exp_int;
}

/* code modified by LLM (iteration 2): added helper lemma to prove exponentiation properties */
lemma ExpSquareProperty(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, 2 * Exp_int(2, n-1)) == Exp_int(x, Exp_int(2, n-1)) * Exp_int(x, Exp_int(2, n-1))
{
  reveal Exp_int;
  ExpMultiplicationProperty(x, Exp_int(2, n-1), Exp_int(2, n-1));
}

/* code modified by LLM (iteration 2): added modular arithmetic lemma */
lemma ModularMultiplicationProperty(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

// computes res := x^y % z when y == 2^n (repeated squaring)
method ModExpPow2_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y == Exp_int(2, n)
  requires z > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
  if n == 0 {
    /* code modified by LLM (iteration 2): fixed base case - when n=0, y=1, so we need x^1 % z */
    reveal Exp_int;
    res := x % z;
  } else {
    /* code modified by LLM (iteration 2): fixed recursive call with correct parameters */
    var temp := ModExpPow2_int(x, Exp_int(2, n-1), n-1, z);
    
    // Establish the mathematical relationships
    PowerOf2Property(n);
    ExpSquareProperty(x, n);
    ModularMultiplicationProperty(Exp_int(x, Exp_int(2, n-1)), Exp_int(x, Exp_int(2, n-1)), z);
    
    /* code modified by LLM (iteration 2): apply modular arithmetic correctly */
    res := (temp * temp) % z;
  }
}