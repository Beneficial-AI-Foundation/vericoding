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
    /* code modified by LLM (iteration 1): fixed base case with lemma application */
    ExpPow2BaseLemma(x, z);
    res := x % z;
  } else {
    /* code modified by LLM (iteration 1): recursive call with correct parameters */
    var temp := ModExpPow2_int(x, Exp_int(2, n-1), n-1, z);
    /* code modified by LLM (iteration 1): apply correctness lemma before computation */
    ExpPow2Lemma(x, n, z);
    res := (temp * temp) % z;
  }
}

/* code modified by LLM (iteration 1): base case lemma for n=0 */
lemma ExpPow2BaseLemma(x: nat, z: nat)
  requires z > 0
  ensures Exp_int(x, Exp_int(2, 0)) % z == x % z
{
  reveal Exp_int;
}

/* code modified by LLM (iteration 1): main correctness lemma */
lemma ExpPow2Lemma(x: nat, n: nat, z: nat)
  requires n > 0
  requires z > 0
  ensures Exp_int(x, Exp_int(2, n)) % z == ((Exp_int(x, Exp_int(2, n-1)) % z) * (Exp_int(x, Exp_int(2, n-1)) % z)) % z
{
  reveal Exp_int;
  var k := Exp_int(2, n-1);
  
  /* code modified by LLM (iteration 1): establish basic properties */
  assert Exp_int(2, n) == 2 * k;
  
  /* code modified by LLM (iteration 1): use exponent doubling property */
  ExpDoubleProperty(x, k);
  
  /* code modified by LLM (iteration 1): apply modulo property */
  var xk := Exp_int(x, k);
  ModuloSquareLemma(xk, z);
  
  /* code modified by LLM (iteration 1): establish the connection */
  assert Exp_int(x, Exp_int(2, n)) == Exp_int(x, 2 * k);
  assert Exp_int(x, 2 * k) == xk * xk;
}

/* code modified by LLM (iteration 1): lemma for x^(2*k) = (x^k)^2 */
lemma ExpDoubleProperty(x: nat, k: nat)
  ensures Exp_int(x, 2 * k) == Exp_int(x, k) * Exp_int(x, k)
{
  reveal Exp_int;
  ExpAddProperty(x, k, k);
  assert Exp_int(x, k + k) == Exp_int(x, k) * Exp_int(x, k);
  assert k + k == 2 * k;
}

/* code modified by LLM (iteration 1): lemma for x^(a+b) = x^a * x^b */
lemma ExpAddProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases a
{
  reveal Exp_int;
  if a == 0 {
    /* code modified by LLM (iteration 1): base case */
    assert Exp_int(x, 0) == 1;
  } else {
    /* code modified by LLM (iteration 1): inductive step */
    ExpAddProperty(x, a - 1, b);
    assert Exp_int(x, a + b) == x * Exp_int(x, (a - 1) + b);
    assert Exp_int(x, (a - 1) + b) == Exp_int(x, a - 1) * Exp_int(x, b);
    assert Exp_int(x, a) == x * Exp_int(x, a - 1);
  }
}

/* code modified by LLM (iteration 1): lemma for modulo property of squares */
lemma ModuloSquareLemma(temp: nat, z: nat)
  requires z > 0
  ensures (temp * temp) % z == ((temp % z) * (temp % z)) % z
{
  /* code modified by LLM (iteration 1): use modular arithmetic property */
  var r := temp % z;
  assert temp == (temp / z) * z + r;
  
  /* code modified by LLM (iteration 1): expand and simplify */
  calc {
    (temp * temp) % z;
    == (((temp / z) * z + r) * ((temp / z) * z + r)) % z;
    == ((temp / z) * (temp / z) * z * z + 2 * (temp / z) * z * r + r * r) % z;
    == (r * r) % z;
    == ((temp % z) * (temp % z)) % z;
  }
}