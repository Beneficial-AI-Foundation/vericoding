//ATOM

// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

/* code modified by LLM (iteration 4): Added helper lemma to establish exponentiation properties */
lemma ExpMultProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a * b) == Exp_int(Exp_int(x, a), b)
{
  reveal Exp_int();
  if b == 0 {
    assert a * b == 0;
  } else {
    ExpMultProperty(x, a, b - 1);
  }
}

/* code modified by LLM (iteration 4): Added helper lemma for power of 2 properties */
lemma Pow2Property(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n - 1)
{
  reveal Exp_int();
}

/* code modified by LLM (iteration 4): Added helper lemma for modular arithmetic property */
lemma ModSquareProperty(a: nat, z: nat)
  requires z > 0
  ensures (a * a) % z == ((a % z) * (a % z)) % z
{
  // This follows from properties of modular arithmetic
}

/* code modified by LLM (iteration 4): Added lemma for modular exponentiation correctness */
lemma ModExpCorrectness(base: nat, exp: nat, mod: nat, computed: nat)
  requires mod > 0
  requires computed == Exp_int(base, exp) % mod
  ensures computed == Exp_int(base, exp) % mod
{
  // Tautology to help with verification
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
    /* code modified by LLM (iteration 4): Fixed base case with proper reasoning */
    reveal Exp_int();
    assert y == Exp_int(2, 0) == 1;
    assert Exp_int(x, y) == Exp_int(x, 1) == x;
    res := x % z;
  } else {
    /* code modified by LLM (iteration 4): Restructured recursive case with clearer mathematical reasoning */
    var half_exp := Exp_int(2, n-1);
    
    // Establish that y == 2 * half_exp
    Pow2Property(n);
    assert y == 2 * half_exp;
    
    // Get the result for the smaller exponent
    var temp := ModExpPow2_int(x, half_exp, n-1, z);
    
    // temp satisfies the postcondition: temp == Exp_int(x, half_exp) % z
    assert temp == Exp_int(x, half_exp) % z;
    
    // Establish the mathematical relationship: x^(2*half_exp) == (x^half_exp)^2
    ExpMultProperty(x, half_exp, 2);
    assert Exp_int(x, y) == Exp_int(x, 2 * half_exp) == Exp_int(Exp_int(x, half_exp), 2);
    
    // Simplify (x^half_exp)^2 to x^half_exp * x^half_exp
    reveal Exp_int();
    assert Exp_int(Exp_int(x, half_exp), 2) == Exp_int(x, half_exp) * Exp_int(x, half_exp);
    
    // Apply modular arithmetic: (a*a) % z == ((a%z) * (a%z)) % z
    ModSquareProperty(Exp_int(x, half_exp), z);
    
    /* code modified by LLM (iteration 4): Final computation with explicit reasoning */
    res := (temp * temp) % z;
    
    // Verify the result
    assert res == (temp * temp) % z;
    assert res == ((Exp_int(x, half_exp) % z) * (Exp_int(x, half_exp) % z)) % z;
    assert res == (Exp_int(x, half_exp) * Exp_int(x, half_exp)) % z;
    assert res == Exp_int(x, y) % z;
  }
}