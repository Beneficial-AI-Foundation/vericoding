//ATOM
// Computation of x^n in time and space O(log n).
method powerDC(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  /* code modified by LLM (iteration 2): Fixed divide-and-conquer implementation with proper verification */
  if n == 0 {
    p := 1.0;
  } else if n == 1 {
    p := x;
  } else {
    var half := n / 2;
    var temp := powerDC(x, half);
    if n % 2 == 0 {
      p := temp * temp;
      /* code modified by LLM (iteration 2): Added assertion to help verification */
      assert p == power(x, half) * power(x, half);
      powerLemmaEven(x, n, half);
    } else {
      p := temp * temp * x;
      /* code modified by LLM (iteration 2): Added assertion to help verification */
      assert p == power(x, half) * power(x, half) * x;
      powerLemmaOdd(x, n, half);
    }
  }
}

//ATOM
// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {
  if n == 0 then 1.0 else x * power(x, n-1)
}

/* code modified by LLM (iteration 2): Added helper lemmas for verification */
lemma powerLemmaEven(x: real, n: nat, half: nat)
  requires n >= 2
  requires half == n / 2
  requires n % 2 == 0
  ensures power(x, n) == power(x, half) * power(x, half)
{
  assert n == half + half;
  powerAdditive(x, half, half);
}

/* code modified by LLM (iteration 2): Added helper lemmas for verification */
lemma powerLemmaOdd(x: real, n: nat, half: nat)
  requires n >= 2
  requires half == n / 2
  requires n % 2 == 1
  ensures power(x, n) == power(x, half) * power(x, half) * x
{
  assert n == half + half + 1;
  powerAdditive(x, half, half + 1);
  powerAdditive(x, half, 1);
}

/* code modified by LLM (iteration 2): Added fundamental power lemma */
lemma powerAdditive(x: real, m: nat, n: nat)
  ensures power(x, m + n) == power(x, m) * power(x, n)
{
  if n == 0 {
    assert power(x, m + 0) == power(x, m);
    assert power(x, 0) == 1.0;
  } else {
    powerAdditive(x, m, n - 1);
    assert power(x, m + n) == x * power(x, m + n - 1);
    assert power(x, m + n - 1) == power(x, m) * power(x, n - 1);
    assert power(x, n) == x * power(x, n - 1);
  }
}

// SPEC
// A few test cases (checked statically by Dafny).
method testPowerDC() {
  /* code modified by LLM (iteration 2): Added test cases with assertions */
  var result1 := powerDC(2.0, 0);
  assert result1 == 1.0;
  
  var result2 := powerDC(2.0, 1);
  assert result2 == 2.0;
  
  var result3 := powerDC(2.0, 3);
  assert result3 == 8.0;
  
  var result4 := powerDC(3.0, 2);
  assert result4 == 9.0;
}