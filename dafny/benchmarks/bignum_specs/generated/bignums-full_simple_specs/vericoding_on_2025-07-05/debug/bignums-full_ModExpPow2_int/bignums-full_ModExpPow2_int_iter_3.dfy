//ATOM

// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

/* code modified by LLM (iteration 2): Added helper lemma to establish the mathematical relationship for repeated squaring */
lemma ExpSquareProperty(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  reveal Exp_int();
  if n == 1 {
    // Base case: 2^1 = 2, so x^(2^1) = x^2 = (x^(2^0))^2 = (x^1)^2
    assert Exp_int(2, 1) == 2;
    assert Exp_int(2, 0) == 1;
  } else {
    // Inductive case: use the fact that 2^n = 2 * 2^(n-1)
    ExpSquareProperty(x, n-1);
    assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
  }
}

/* code modified by LLM (iteration 2): Added helper lemma for modular arithmetic property */
lemma ModSquareProperty(a: nat, z: nat)
  requires z > 0
  ensures (a * a) % z == ((a % z) * (a % z)) % z
{
  // This follows from properties of modular arithmetic
}

//IMPL 

// computes res := x^y % z when y == 2^n (repeated squaring)
method ModExpPow2_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y == Exp_int(2, n)
  requires z > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
  if n == 0 {
    /* code modified by LLM (iteration 2): Fixed base case - when n=0, y=2^0=1, so x^y = x^1 = x */
    reveal Exp_int();
    res := x % z;
  } else {
    /* code modified by LLM (iteration 2): Fixed recursive call with correct arguments */
    var temp := ModExpPow2_int(x, Exp_int(2, n-1), n-1, z);
    
    /* code modified by LLM (iteration 2): Added lemma calls to establish the mathematical relationships */
    ExpSquareProperty(x, n);
    ModSquareProperty(temp, z);
    
    /* code modified by LLM (iteration 2): Added assertion to show the mathematical equivalence */
    assert Exp_int(x, y) == Exp_int(temp, 2);
    
    res := (temp * temp) % z;
  }
}