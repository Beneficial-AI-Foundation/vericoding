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
    /* code modified by LLM (iteration 1): fixed base case to return 1 % z when y == 1 */
    res := 1 % z;
  } else {
    /* code modified by LLM (iteration 1): fixed recursive call arguments and added helper lemma */
    var temp := ModExpPow2_int(x, Exp_int(2, n-1), n-1, z);
    res := (temp * temp) % z;
    
    /* code modified by LLM (iteration 1): added lemma call to establish mathematical correctness */
    ExpPow2Lemma(x, n);
  }
}

/* code modified by LLM (iteration 1): added helper lemma to prove x^(2^n) = (x^(2^(n-1)))^2 */
lemma ExpPow2Lemma(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  reveal Exp_int;
  ExpDoubleProperty(x, Exp_int(2, n-1));
}

/* code modified by LLM (iteration 1): added helper lemma for exponent doubling property */
lemma ExpDoubleProperty(x: nat, k: nat)
  ensures Exp_int(x, 2 * k) == Exp_int(Exp_int(x, k), 2)
{
  reveal Exp_int;
  if k == 0 {
    // Base case: x^0 = 1, so x^(2*0) = x^0 = 1 and (x^0)^2 = 1^2 = 1
  } else {
    // Inductive case
    ExpDoubleProperty(x, k - 1);
    ExpAddProperty(x, k, k);
  }
}

/* code modified by LLM (iteration 1): added helper lemma for exponent addition property */
lemma ExpAddProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  reveal Exp_int;
  if a == 0 {
    // Base case
  } else {
    ExpAddProperty(x, a - 1, b);
  }
}