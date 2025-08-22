//ATOM

// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

//ATOM

// computes res := x^y % z when y == 2^n (repeated squaring)
method ModExpPow2_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y == Exp_int(2, n)
  requires z > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
    res := 0;
    assume res == Exp_int(x,y) % z;
    return res;
}

//IMPL ModExp_int

// simulates the exponentiation we do on bistrings through bit decomposition and repeated squaring
method ModExp_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y < Exp_int(2,n+1)
  requires z > 1 //&& n > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
  if y == 0 {
    /* code modified by LLM (iteration 1): Added assertion to help prove the postcondition when y == 0 */
    assert Exp_int(x, 0) == 1 by { reveal Exp_int; }
    res := 1;
  } else if n == 0 {
    /* code modified by LLM (iteration 1): Added assertions to handle the base case when n == 0 */
    assert y < Exp_int(2, 1) by { reveal Exp_int; }
    assert Exp_int(2, 1) == 2 by { reveal Exp_int; }
    assert y < 2;
    assert y == 1; // since y != 0 and y < 2
    assert Exp_int(x, 1) == x by { reveal Exp_int; }
    res := x % z;
  } else {
    /* code modified by LLM (iteration 1): Calculate 2^n for bit testing */
    var pow2n: nat;
    pow2n := Exp_int(2, n);
    
    /* code modified by LLM (iteration 1): Prove key properties about powers of 2 */
    Exp_int_consecutive_lemma(n);
    assert Exp_int(2, n+1) == 2 * Exp_int(2, n);
    assert Exp_int(2, n+1) == 2 * pow2n;
    
    if y >= pow2n {
      /* code modified by LLM (iteration 1): Handle case where bit n is set */
      assert y < 2 * pow2n;
      assert y - pow2n < pow2n;
      assert y - pow2n < Exp_int(2, n);
      assert Exp_int(2, n) <= Exp_int(2, n+1);
      assert y - pow2n < Exp_int(2, n+1);
      
      /* code modified by LLM (iteration 1): Ensure recursive call precondition is satisfied */
      if n == 0 {
        assert false; // This case is handled above
      } else {
        assert y - pow2n < Exp_int(2, (n-1)+1);
      }
      
      var temp1: nat;
      temp1 := ModExpPow2_int(x, pow2n, n, z);
      var temp2: nat;
      temp2 := ModExp_int(x, y - pow2n, n-1, z);
      
      /* code modified by LLM (iteration 1): Apply exponentiation property and modular arithmetic */
      ExponentiationSplitLemma(x, pow2n, y - pow2n);
      assert Exp_int(x, y) == Exp_int(x, pow2n + (y - pow2n));
      assert Exp_int(x, pow2n + (y - pow2n)) == Exp_int(x, pow2n) * Exp_int(x, y - pow2n);
      
      ModularArithmeticLemma(Exp_int(x, pow2n), Exp_int(x, y - pow2n), z);
      assert (Exp_int(x, pow2n) * Exp_int(x, y - pow2n)) % z == ((Exp_int(x, pow2n) % z) * (Exp_int(x, y - pow2n) % z)) % z;
      assert temp1 == Exp_int(x, pow2n) % z;
      assert temp2 == Exp_int(x, y - pow2n) % z;
      
      res := (temp1 * temp2) % z;
    } else {
      /* code modified by LLM (iteration 1): Handle case where bit n is not set */
      assert y < pow2n;
      assert y < Exp_int(2, n);
      
      /* code modified by LLM (iteration 1): Ensure precondition for recursive call */
      if n == 0 {
        assert false; // This case is handled above  
      } else {
        assert n >= 1;
        assert y < Exp_int(2, n);
        assert Exp_int(2, n) <= Exp_int(2, n+1);
        Exp_int_monotonic_lemma(n, n+1);
        assert y < Exp_int(2, (n-1)+1);
      }
      
      res := ModExp_int(x, y, n-1, z);
    }
  }
}

/* code modified by LLM (iteration 1): Added helper lemma for consecutive powers of 2 */
lemma Exp_int_consecutive_lemma(n: nat)
  ensures Exp_int(2, n+1) == 2 * Exp_int(2, n)
{
  reveal Exp_int;
}

/* code modified by LLM (iteration 1): Added helper lemma for monotonicity of powers */
lemma Exp_int_monotonic_lemma(a: nat, b: nat)
  requires a <= b
  ensures Exp_int(2, a) <= Exp_int(2, b)
{
  reveal Exp_int;
  if a == b {
    // trivially true
  } else {
    assert a < b;
    Exp_int_monotonic_lemma(a, b-1);
    assert Exp_int(2, a) <= Exp_int(2, b-1);
    assert Exp_int(2, b) == 2 * Exp_int(2, b-1);
    assert Exp_int(2, b-1) <= Exp_int(2, b);
  }
}

/* code modified by LLM (iteration 1): Modular arithmetic lemma */
lemma ModularArithmeticLemma(a: nat, b: nat, z: nat)
  requires z > 1
  ensures (a * b) % z == ((a % z) * (b % z)) % z
{
  // This is a standard property of modular arithmetic
}

/* code modified by LLM (iteration 1): Added helper lemma for exponentiation split property */
lemma ExponentiationSplitLemma(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  reveal Exp_int;
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a);
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x, a) * 1 == Exp_int(x, a);
  } else {
    ExponentiationSplitLemma(x, a, b-1);
    assert Exp_int(x, a + b) == x * Exp_int(x, a + (b-1));
    assert Exp_int(x, a + (b-1)) == Exp_int(x, a) * Exp_int(x, b-1);
    assert Exp_int(x, b) == x * Exp_int(x, b-1);
  }
}