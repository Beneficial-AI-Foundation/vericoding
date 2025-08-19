//ATOM

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
  if n == 0 then 1.0 else x * power(x, n-1)
}

//IMPL testPowerOpt

/* code modified by LLM (iteration 1): Removed invalid text and added helper lemmas for exponentiation by squaring */

lemma PowerSquareHalve(base: real, exp: nat)
  requires exp % 2 == 0
  ensures power(base * base, exp / 2) == power(base, exp)
{
  if exp == 0 {
    // base case: power(anything, 0) == 1.0
  } else {
    // inductive case: we need to prove power(base^2, exp/2) == power(base, exp)
    // where exp is even
    var half_exp := exp / 2;
    assert exp == 2 * half_exp;
    PowerSquareHalveHelper(base, half_exp);
  }
}

lemma PowerSquareHalveHelper(base: real, k: nat)
  ensures power(base * base, k) == power(base, 2 * k)
{
  if k == 0 {
    // base case
  } else {
    // inductive case
    PowerSquareHalveHelper(base, k - 1);
    assert power(base * base, k) == (base * base) * power(base * base, k - 1);
    assert power(base * base, k - 1) == power(base, 2 * (k - 1));
    assert power(base, 2 * k) == base * power(base, 2 * k - 1);
    assert power(base, 2 * k - 1) == base * power(base, 2 * (k - 1));
  }
}

method powerOpt(x: real, n: nat) returns (p : real)
ensures p == power(x, n)
{
  /* code modified by LLM (iteration 1): Fixed loop invariant with helper lemmas and proper invariant maintenance */
  if n == 0 {
    p := 1.0;
  } else {
    var base := x;
    var exp := n;
    p := 1.0;
    
    while exp > 0
      invariant p * power(base, exp) == power(x, n)
      invariant exp >= 0
      decreases exp
    {
      if exp % 2 == 1 {
        /* code modified by LLM (iteration 1): Odd case - multiply p by base and decrement exp */
        p := p * base;
        exp := exp - 1;
      } else {
        /* code modified by LLM (iteration 1): Even case - square base and halve exp using lemma */
        PowerSquareHalve(base, exp);
        assert power(base * base, exp / 2) == power(base, exp);
        base := base * base;
        exp := exp / 2;
      }
    }
  }
}

method testPowerOpt(){
  var result := powerOpt(2.0, 3);
  assert result == power(2.0, 3);
  
  var result2 := powerOpt(5.0, 0);
  assert result2 == power(5.0, 0);
  
  var result3 := powerOpt(1.0, 100);
  assert result3 == power(1.0, 100);
}