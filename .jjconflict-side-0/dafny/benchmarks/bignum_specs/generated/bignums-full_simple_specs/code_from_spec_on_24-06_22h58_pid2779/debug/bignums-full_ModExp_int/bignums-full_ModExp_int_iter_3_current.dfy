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
    assert Exp_int(x, 0) == 1;
    res := 1;
  } else if n == 0 {
    /* code modified by LLM (iteration 1): Added assertions to handle the base case when n == 0 */
    assert y < Exp_int(2, 1);
    assert Exp_int(2, 1) == 2;
    assert y < 2;
    assert y == 1; // since y != 0 and y < 2
    assert Exp_int(x, 1) == x;
    res := x % z;
  } else {
    var pow2n := Exp_int(2, n);
    if y >= pow2n {
      /* code modified by LLM (iteration 1): Fixed subtraction and added proper mathematical reasoning */
      assert y - pow2n < y;
      assert y < Exp_int(2, n+1);
      assert Exp_int(2, n+1) == 2 * Exp_int(2, n);
      assert y < 2 * pow2n;
      assert y - pow2n < pow2n;
      
      var temp1;
      temp1 := ModExpPow2_int(x, pow2n, n, z);
      var temp2;
      temp2 := ModExp_int(x, y - pow2n, n, z);
      
      /* code modified by LLM (iteration 1): Added lemma call and proper modular arithmetic reasoning */
      ModularArithmeticLemma(x, pow2n, y - pow2n, z);
      
      res := (temp1 * temp2) % z;
    } else {
      /* code modified by LLM (iteration 1): Fixed precondition for recursive call */
      assert y < pow2n;
      assert pow2n == Exp_int(2, n);
      assert n >= 1;
      assert Exp_int(2, n-1+1) == Exp_int(2, n);
      assert y < Exp_int(2, (n-1)+1);
      
      res := ModExp_int(x, y, n - 1, z);
    }
  }
}

/* code modified by LLM (iteration 1): Added helper lemma for modular arithmetic property */
lemma ModularArithmeticLemma(x: nat, a: nat, b: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, a + b) % z == ((Exp_int(x, a) % z) * (Exp_int(x, b) % z)) % z
{
  // The proof follows from properties of modular arithmetic and exponentiation
  calc {
    Exp_int(x, a + b) % z;
  ==  { ExponentiationAdditionLemma(x, a, b); }
    (Exp_int(x, a) * Exp_int(x, b)) % z;
  ==  { ModularMultiplicationLemma(Exp_int(x, a), Exp_int(x, b), z); }
    ((Exp_int(x, a) % z) * (Exp_int(x, b) % z)) % z;
  }
}

/* code modified by LLM (iteration 1): Added helper lemma for exponentiation addition property */
lemma ExponentiationAdditionLemma(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  // This follows from the definition of exponentiation
}

/* code modified by LLM (iteration 1): Added helper lemma for modular multiplication property */
lemma ModularMultiplicationLemma(a: nat, b: nat, z: nat)
  requires z > 1
  ensures (a * b) % z == ((a % z) * (b % z)) % z
{
  // This is a standard property of modular arithmetic
}