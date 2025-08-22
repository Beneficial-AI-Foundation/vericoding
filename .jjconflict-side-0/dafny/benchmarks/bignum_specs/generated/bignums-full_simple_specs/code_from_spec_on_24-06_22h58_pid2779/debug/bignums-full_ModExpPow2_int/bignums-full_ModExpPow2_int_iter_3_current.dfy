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
    /* code modified by LLM (iteration 2): fixed base case to return x % z when n=0 (y=1) */
    res := x % z;
  } else {
    /* code modified by LLM (iteration 2): recursive call with correct parameters */
    var temp := ModExpPow2_int(x, Exp_int(2, n-1), n-1, z);
    res := (temp * temp) % z;
    
    /* code modified by LLM (iteration 2): added lemma calls to establish correctness */
    Power2DecompositionLemma(n);
    ExpPow2Lemma(x, n);
  }
}

/* code modified by LLM (iteration 2): lemma to show 2^n = 2 * 2^(n-1) */
lemma Power2DecompositionLemma(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n-1)
{
  reveal Exp_int;
}

/* code modified by LLM (iteration 2): lemma to show x^(2^n) = (x^(2^(n-1)))^2 */
lemma ExpPow2Lemma(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  reveal Exp_int;
  Power2DecompositionLemma(n);
  /* code modified by LLM (iteration 2): use the fact that 2^n = 2 * 2^(n-1) */
  assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
  ExpDoubleProperty(x, Exp_int(2, n-1));
}

/* code modified by LLM (iteration 2): lemma for x^(2*k) = (x^k)^2 */
lemma ExpDoubleProperty(x: nat, k: nat)
  ensures Exp_int(x, 2 * k) == Exp_int(Exp_int(x, k), 2)
{
  reveal Exp_int;
  ExpAddProperty(x, k, k);
  /* code modified by LLM (iteration 2): use x^(k+k) = x^k * x^k = (x^k)^2 */
  assert k + k == 2 * k;
  assert Exp_int(Exp_int(x, k), 2) == Exp_int(x, k) * Exp_int(x, k);
}

/* code modified by LLM (iteration 2): lemma for x^(a+b) = x^a * x^b */
lemma ExpAddProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  reveal Exp_int;
  if a == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x, 0 + b) == Exp_int(x, b);
    assert Exp_int(x, 0) * Exp_int(x, b) == 1 * Exp_int(x, b) == Exp_int(x, b);
  } else {
    /* code modified by LLM (iteration 2): inductive step with proper reasoning */
    ExpAddProperty(x, a - 1, b);
    assert Exp_int(x, (a-1) + b) == Exp_int(x, a-1) * Exp_int(x, b);
    assert a + b == (a - 1) + b + 1;
    assert Exp_int(x, a + b) == x * Exp_int(x, (a-1) + b);
    assert Exp_int(x, a) == x * Exp_int(x, a-1);
  }
}