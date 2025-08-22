//ATOM

// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
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
    /* code modified by LLM (iteration 7): fixed base case with lemma application */
    ExpPow2BaseLemma(x, z);
    res := x % z;
  } else {
    /* code modified by LLM (iteration 7): recursive call with correct parameters */
    var temp := ModExpPow2_int(x, Exp_int(2, n-1), n-1, z);
    /* code modified by LLM (iteration 7): apply correctness lemma before computation */
    ExpPow2Lemma(x, n, z);
    res := (temp * temp) % z;
  }
}

/* code modified by LLM (iteration 7): base case lemma for n=0 */
lemma ExpPow2BaseLemma(x: nat, z: nat)
  requires z > 0
  ensures Exp_int(x, Exp_int(2, 0)) % z == x % z
{
  reveal Exp_int;
  assert Exp_int(2, 0) == 1;
  assert Exp_int(x, 1) == x;
}

/* code modified by LLM (iteration 7): main correctness lemma */
lemma ExpPow2Lemma(x: nat, n: nat, z: nat)
  requires n > 0
  requires z > 0
  ensures Exp_int(x, Exp_int(2, n)) % z == ((Exp_int(x, Exp_int(2, n-1)) % z) * (Exp_int(x, Exp_int(2, n-1)) % z)) % z
{
  reveal Exp_int;
  var k := Exp_int(2, n-1);
  
  /* code modified by LLM (iteration 7): establish 2^n = 2 * 2^(n-1) */
  assert Exp_int(2, n) == 2 * k;
  
  /* code modified by LLM (iteration 7): use exponent doubling property */
  ExpDoubleProperty(x, k);
  
  /* code modified by LLM (iteration 7): apply modulo property of squares */
  var xk := Exp_int(x, k);
  ModuloSquareLemma(xk, z);
}

/* code modified by LLM (iteration 7): lemma for x^(2*k) = (x^k)^2 */
lemma ExpDoubleProperty(x: nat, k: nat)
  ensures Exp_int(x, 2 * k) == Exp_int(Exp_int(x, k), 2)
{
  reveal Exp_int;
  ExpAddProperty(x, k, k);
  /* code modified by LLM (iteration 7): establish equivalences step by step */
  assert Exp_int(x, k + k) == Exp_int(x, k) * Exp_int(x, k);
  assert k + k == 2 * k;
  assert Exp_int(Exp_int(x, k), 2) == Exp_int(x, k) * Exp_int(x, k);
}

/* code modified by LLM (iteration 7): lemma for x^(a+b) = x^a * x^b */
lemma ExpAddProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases a
{
  reveal Exp_int;
  if a == 0 {
    /* code modified by LLM (iteration 7): base case proof */
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x, 0 + b) == Exp_int(x, b);
  } else {
    /* code modified by LLM (iteration 7): inductive step */
    ExpAddProperty(x, a - 1, b);
    assert Exp_int(x, (a - 1) + b) == Exp_int(x, a - 1) * Exp_int(x, b);
    assert Exp_int(x, a) == x * Exp_int(x, a - 1);
    assert a + b == 1 + ((a - 1) + b);
    /* code modified by LLM (iteration 7): arithmetic manipulation */
    calc {
      Exp_int(x, a + b);
      == Exp_int(x, 1 + ((a - 1) + b));
      == x * Exp_int(x, (a - 1) + b);
      == x * (Exp_int(x, a - 1) * Exp_int(x, b));
      == (x * Exp_int(x, a - 1)) * Exp_int(x, b);
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

/* code modified by LLM (iteration 7): lemma for modulo property of squares */
lemma ModuloSquareLemma(temp: nat, z: nat)
  requires z > 0
  ensures (temp * temp) % z == ((temp % z) * (temp % z)) % z
{
  /* code modified by LLM (iteration 7): use division-remainder representation */
  var q := temp / z;
  var r := temp % z;
  assert temp == q * z + r;
  
  /* code modified by LLM (iteration 7): expand (a*z + r)^2 and simplify modulo z */
  calc {
    (temp * temp) % z;
    == ((q * z + r) * (q * z + r)) % z;
    == (q * q * z * z + 2 * q * z * r + r * r) % z;
    == ((q * q * z + 2 * q * r) * z + r * r) % z;
    == (r * r) % z;
    == ((temp % z) * (temp % z)) % z;
  }
}