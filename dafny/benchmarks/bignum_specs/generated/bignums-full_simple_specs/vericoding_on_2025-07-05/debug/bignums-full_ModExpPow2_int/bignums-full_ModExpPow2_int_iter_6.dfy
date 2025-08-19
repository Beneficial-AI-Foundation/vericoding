//ATOM

// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

/* code modified by LLM (iteration 5): Fixed helper lemma with proper inductive proof */
lemma ExpMultProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a * b) == Exp_int(Exp_int(x, a), b)
{
  reveal Exp_int();
  if b == 0 {
    assert a * b == 0;
    assert Exp_int(x, a * b) == Exp_int(x, 0) == 1;
    assert Exp_int(Exp_int(x, a), b) == Exp_int(Exp_int(x, a), 0) == 1;
  } else {
    ExpMultProperty(x, a, b - 1);
    assert Exp_int(x, a * (b - 1)) == Exp_int(Exp_int(x, a), b - 1);
    assert a * b == a * (b - 1) + a;
    ExpAddProperty(x, a * (b - 1), a);
    assert Exp_int(x, a * b) == Exp_int(x, a * (b - 1) + a) == Exp_int(x, a * (b - 1)) * Exp_int(x, a);
    assert Exp_int(x, a * b) == Exp_int(Exp_int(x, a), b - 1) * Exp_int(x, a);
    assert Exp_int(Exp_int(x, a), b) == Exp_int(x, a) * Exp_int(Exp_int(x, a), b - 1);
  }
}

/* code modified by LLM (iteration 5): Added missing exponent addition property */
lemma ExpAddProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  reveal Exp_int();
  if b == 0 {
    assert a + b == a;
    assert Exp_int(x, b) == 1;
  } else {
    ExpAddProperty(x, a, b - 1);
    assert Exp_int(x, a + (b - 1)) == Exp_int(x, a) * Exp_int(x, b - 1);
    assert a + b == a + (b - 1) + 1;
    assert Exp_int(x, a + b) == x * Exp_int(x, a + (b - 1));
    assert Exp_int(x, a + b) == x * Exp_int(x, a) * Exp_int(x, b - 1);
    assert Exp_int(x, b) == x * Exp_int(x, b - 1);
    assert Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b);
  }
}

/* code modified by LLM (iteration 5): Simplified power of 2 property */
lemma Pow2Property(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n - 1)
{
  reveal Exp_int();
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
    /* code modified by LLM (iteration 5): Simplified base case */
    reveal Exp_int();
    assert y == Exp_int(2, 0) == 1;
    res := x % z;
  } else {
    /* code modified by LLM (iteration 5): Restructured with clearer mathematical steps */
    var half_exp := Exp_int(2, n-1);
    
    // Establish relationship between y and half_exp
    Pow2Property(n);
    assert y == 2 * half_exp;
    
    // Recursive call
    var temp := ModExpPow2_int(x, half_exp, n-1, z);
    
    // Use exponent properties to establish x^y == (x^half_exp)^2
    assert y == 2 * half_exp;
    ExpMultProperty(x, half_exp, 2);
    assert Exp_int(x, y) == Exp_int(x, 2 * half_exp) == Exp_int(Exp_int(x, half_exp), 2);
    
    reveal Exp_int();
    assert Exp_int(Exp_int(x, half_exp), 2) == Exp_int(x, half_exp) * Exp_int(x, half_exp);
    
    /* code modified by LLM (iteration 5): Final computation with modular arithmetic */
    res := (temp * temp) % z;
    
    // The modular arithmetic property (a*b) % z == ((a%z) * (b%z)) % z is built into Dafny
    assert temp == Exp_int(x, half_exp) % z;
    assert res == (temp * temp) % z;
    assert res == ((Exp_int(x, half_exp) % z) * (Exp_int(x, half_exp) % z)) % z;
    assert res == (Exp_int(x, half_exp) * Exp_int(x, half_exp)) % z;
    assert res == Exp_int(x, y) % z;
  }
}