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
    /* code modified by LLM (iteration 3): fixed base case - when n=0, y=2^0=1, so x^y=x^1=x */
    res := x % z;
  } else {
    /* code modified by LLM (iteration 3): recursive call and squaring step */
    var temp := ModExpPow2_int(x, Exp_int(2, n-1), n-1, z);
    res := (temp * temp) % z;
    
    /* code modified by LLM (iteration 3): establish correctness with lemmas */
    Power2DecompositionLemma(n);
    ExpPow2Lemma(x, n);
    ModuloSquareLemma(temp, z);
  }
}

/* code modified by LLM (iteration 3): lemma to show 2^n = 2 * 2^(n-1) for n > 0 */
lemma Power2DecompositionLemma(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n-1)
{
  reveal Exp_int;
}

/* code modified by LLM (iteration 3): lemma to show x^(2^n) = (x^(2^(n-1)))^2 */
lemma ExpPow2Lemma(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  reveal Exp_int;
  Power2DecompositionLemma(n);
  var k := Exp_int(2, n-1);
  assert Exp_int(2, n) == 2 * k;
  ExpDoubleProperty(x, k);
}

/* code modified by LLM (iteration 3): lemma for x^(2*k) = (x^k)^2 */
lemma ExpDoubleProperty(x: nat, k: nat)
  ensures Exp_int(x, 2 * k) == Exp_int(Exp_int(x, k), 2)
{
  reveal Exp_int;
  if k == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x, 2 * 0) == Exp_int(x, 0) == 1;
    assert Exp_int(1, 2) == 1 * 1 == 1;
  } else {
    /* code modified by LLM (iteration 3): use induction and addition property */
    ExpAddProperty(x, k, k);
    assert Exp_int(x, k + k) == Exp_int(x, k) * Exp_int(x, k);
    assert k + k == 2 * k;
    assert Exp_int(Exp_int(x, k), 2) == Exp_int(x, k) * Exp_int(x, k);
  }
}

/* code modified by LLM (iteration 3): lemma for x^(a+b) = x^a * x^b */
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
    /* code modified by LLM (iteration 3): inductive step with clearer reasoning */
    ExpAddProperty(x, a - 1, b);
    assert Exp_int(x, (a - 1) + b) == Exp_int(x, a - 1) * Exp_int(x, b);
    assert Exp_int(x, a) == x * Exp_int(x, a - 1) by reveal Exp_int;
    assert a + b == 1 + ((a - 1) + b);
    assert Exp_int(x, a + b) == x * Exp_int(x, (a - 1) + b) by reveal Exp_int;
    assert Exp_int(x, a + b) == x * (Exp_int(x, a - 1) * Exp_int(x, b));
    assert Exp_int(x, a + b) == (x * Exp_int(x, a - 1)) * Exp_int(x, b);
    assert Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b);
  }
}

/* code modified by LLM (iteration 3): lemma for modulo property of squares */
lemma ModuloSquareLemma(temp: nat, z: nat)
  requires z > 0
  ensures (temp * temp) % z == ((temp % z) * (temp % z)) % z
{
  /* code modified by LLM (iteration 3): modular arithmetic property */
  var t_mod := temp % z;
  assert temp == (temp / z) * z + t_mod;
  assert (temp * temp) % z == ((temp / z) * z + t_mod) * ((temp / z) * z + t_mod) % z;
  ModuloDistributionLemma(temp, z);
}

/* code modified by LLM (iteration 3): helper lemma for modulo distribution */
lemma ModuloDistributionLemma(a: nat, m: nat)
  requires m > 0
  ensures (a * a) % m == ((a % m) * (a % m)) % m
{
  var q := a / m;
  var r := a % m;
  assert a == q * m + r;
  assert a * a == (q * m + r) * (q * m + r);
  assert a * a == q * m * q * m + 2 * q * m * r + r * r;
  assert a * a == (q * q * m + 2 * q * r) * m + r * r;
  assert (a * a) % m == (r * r) % m;
  assert r * r == (a % m) * (a % m);
  assert ((a % m) * (a % m)) % m == (r * r) % m;
}