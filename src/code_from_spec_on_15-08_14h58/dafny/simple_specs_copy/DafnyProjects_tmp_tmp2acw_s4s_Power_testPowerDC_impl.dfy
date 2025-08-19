method powerDC(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  /* code modified by LLM (iteration 2): Added lemma calls to prove correctness */
  if n == 0 {
    p := 1.0;
  } else if n == 1 {
    p := x;
  } else {
    var half := powerDC(x, n / 2);
    if n % 2 == 0 {
      powerEvenLemma(x, n);
      p := half * half;
    } else {
      powerOddLemma(x, n);
      p := x * half * half;
    }
  }
}

/* code modified by LLM (iteration 2): Added helper lemma for even powers */
lemma powerEvenLemma(x: real, n: nat)
  requires n > 0 && n % 2 == 0
  ensures power(x, n) == power(x, n / 2) * power(x, n / 2)
{
  var half := n / 2;
  assert n == half + half;
  powerAddLemma(x, half, half);
}

/* code modified by LLM (iteration 2): Added helper lemma for odd powers */
lemma powerOddLemma(x: real, n: nat)
  requires n > 0 && n % 2 == 1
  ensures power(x, n) == x * power(x, n / 2) * power(x, n / 2)
{
  var half := n / 2;
  assert n == half + half + 1;
  powerAddLemma(x, half, half);
  powerAddLemma(x, half + half, 1);
}

/* code modified by LLM (iteration 2): Added fundamental lemma about power addition */
lemma powerAddLemma(x: real, m: nat, n: nat)
  ensures power(x, m + n) == power(x, m) * power(x, n)
{
  if m == 0 {
    assert power(x, 0 + n) == power(x, n);
    assert power(x, 0) * power(x, n) == 1.0 * power(x, n) == power(x, n);
  } else {
    powerAddLemma(x, m - 1, n);
    assert power(x, m + n) == x * power(x, (m - 1) + n);
    assert power(x, (m - 1) + n) == power(x, m - 1) * power(x, n);
    assert power(x, m + n) == x * power(x, m - 1) * power(x, n);
    assert power(x, m) == x * power(x, m - 1);
    assert power(x, m + n) == power(x, m) * power(x, n);
  }
}


//ATOM

// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {
  if n == 0 then 1.0 else x * power(x, n-1)
}


//IMPL 

// A few test cases (checked statically by Dafny).
method testPowerDC() {
  // Test case 1: any number to power 0 should be 1
  assert power(5.0, 0) == 1.0;
  assert power(0.0, 0) == 1.0;
  assert power(-3.0, 0) == 1.0;
  
  // Test case 2: any number to power 1 should be itself
  assert power(7.0, 1) == 7.0;
  assert power(-2.0, 1) == -2.0;
  assert power(0.0, 1) == 0.0;
  
  // Test case 3: simple powers
  assert power(2.0, 2) == 4.0;
  assert power(3.0, 2) == 9.0;
  assert power(2.0, 3) == 8.0;
  
  // Test case 4: negative base with even/odd powers
  assert power(-2.0, 2) == 4.0;
  assert power(-2.0, 3) == -8.0;
  
  // Test case 5: zero base (except for 0^0 which equals 1 by our definition)
  assert power(0.0, 5) == 0.0;
}