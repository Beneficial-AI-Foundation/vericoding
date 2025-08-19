//ATOM

// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

/* code modified by LLM (iteration 3): Added helper lemma to establish exponentiation properties */
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

/* code modified by LLM (iteration 3): Added helper lemma for power of 2 properties */
lemma Pow2Property(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n - 1)
{
  reveal Exp_int();
}

/* code modified by LLM (iteration 3): Added helper lemma for modular arithmetic property */
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
    /* code modified by LLM (iteration 3): Fixed base case - when n=0, y=2^0=1, so x^y = x^1 = x */
    reveal Exp_int();
    assert y == 1;
    assert Exp_int(x, y) == x;
    res := x % z;
  } else {
    /* code modified by LLM (iteration 3): Fixed recursive call - compute x^(2^(n-1)) first */
    var half_exp := Exp_int(2, n-1);
    var temp := ModExpPow2_int(x, half_exp, n-1, z);
    
    /* code modified by LLM (iteration 3): Establish the mathematical relationship */
    Pow2Property(n);
    assert y == 2 * half_exp;
    ExpMultProperty(x, half_exp, 2);
    assert Exp_int(x, y) == Exp_int(x, 2 * half_exp);
    assert Exp_int(x, 2 * half_exp) == Exp_int(Exp_int(x, half_exp), 2);
    
    /* code modified by LLM (iteration 3): Use modular arithmetic property */
    reveal Exp_int();
    assert Exp_int(Exp_int(x, half_exp), 2) == Exp_int(x, half_exp) * Exp_int(x, half_exp);
    ModSquareProperty(Exp_int(x, half_exp), z);
    
    /* code modified by LLM (iteration 3): Since temp ≡ x^(2^(n-1)) (mod z), we have temp² ≡ (x^(2^(n-1)))² (mod z) */
    assert temp == Exp_int(x, half_exp) % z;
    
    res := (temp * temp) % z;
  }
}