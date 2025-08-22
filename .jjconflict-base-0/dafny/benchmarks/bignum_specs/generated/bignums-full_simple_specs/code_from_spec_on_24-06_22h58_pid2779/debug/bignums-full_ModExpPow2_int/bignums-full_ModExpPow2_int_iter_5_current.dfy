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
    /* code modified by LLM (iteration 4): fixed base case - when n=0, y=2^0=1, so x^y=x^1=x */
    res := x % z;
  } else {
    /* code modified by LLM (iteration 4): recursive call with correct parameters */
    var temp := ModExpPow2_int(x, Exp_int(2, n-1), n-1, z);
    res := (temp * temp) % z;
    
    /* code modified by LLM (iteration 4): establish correctness with key lemma */
    ExpPow2Lemma(x, n, z);
  }
}

/* code modified by LLM (iteration 4): main correctness lemma */
lemma ExpPow2Lemma(x: nat, n: nat, z: nat)
  requires n > 0
  requires z > 0
  ensures Exp_int(x, Exp_int(2, n)) % z == ((Exp_int(x, Exp_int(2, n-1)) % z) * (Exp_int(x, Exp_int(2, n-1)) % z)) % z
{
  reveal Exp_int;
  var k := Exp_int(2, n-1);
  
  /* code modified by LLM (iteration 4): show 2^n = 2 * 2^(n-1) */
  assert Exp_int(2, n) == 2 * k;
  
  /* code modified by LLM (iteration 4): use exponent doubling property */
  ExpDoubleProperty(x, k);
  assert Exp_int(x, 2 * k) == Exp_int(Exp_int(x, k), 2);
  assert Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, k), 2);
  
  /* code modified by LLM (iteration 4): expand square definition */
  assert Exp_int(Exp_int(x, k), 2) == Exp_int(x, k) * Exp_int(x, k);
  
  /* code modified by LLM (iteration 4): apply modulo property */
  ModuloSquareLemma(Exp_int(x, k), z);
}

/* code modified by LLM (iteration 4): lemma for x^(2*k) = (x^k)^2 */
lemma ExpDoubleProperty(x: nat, k: nat)
  ensures Exp_int(x, 2 * k) == Exp_int(Exp_int(x, k), 2)
{
  reveal Exp_int;
  ExpAddProperty(x, k, k);
  assert Exp_int(x, k + k) == Exp_int(x, k) * Exp_int(x, k);
  assert k + k == 2 * k;
  assert Exp_int(Exp_int(x, k), 2) == Exp_int(x, k) * Exp_int(x, k);
}

/* code modified by LLM (iteration 4): lemma for x^(a+b) = x^a * x^b */
lemma ExpAddProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases a
{
  reveal Exp_int;
  if a == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x, 0 + b) == Exp_int(x, b);
    assert Exp_int(x, 0) * Exp_int(x, b) == 1 * Exp_int(x, b) == Exp_int(x, b);
  } else {
    ExpAddProperty(x, a - 1, b);
    assert Exp_int(x, (a - 1) + b) == Exp_int(x, a - 1) * Exp_int(x, b);
    assert Exp_int(x, a) == x * Exp_int(x, a - 1);
    assert a + b == 1 + ((a - 1) + b);
    assert Exp_int(x, a + b) == x * Exp_int(x, (a - 1) + b);
    assert Exp_int(x, a + b) == x * (Exp_int(x, a - 1) * Exp_int(x, b));
    assert Exp_int(x, a + b) == (x * Exp_int(x, a - 1)) * Exp_int(x, b);
    assert Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b);
  }
}

/* code modified by LLM (iteration 4): lemma for modulo property of squares */
lemma ModuloSquareLemma(temp: nat, z: nat)
  requires z > 0
  ensures (temp * temp) % z == ((temp % z) * (temp % z)) % z
{
  var q := temp / z;
  var r := temp % z;
  assert temp == q * z + r;
  assert temp * temp == (q * z + r) * (q * z + r);
  assert temp * temp == q * z * q * z + 2 * q * z * r + r * r;
  assert temp * temp == (q * q * z + 2 * q * r) * z + r * r;
  assert (temp * temp) % z == (r * r) % z;
  assert r == temp % z;
  assert (r * r) % z == ((temp % z) * (temp % z)) % z;
}