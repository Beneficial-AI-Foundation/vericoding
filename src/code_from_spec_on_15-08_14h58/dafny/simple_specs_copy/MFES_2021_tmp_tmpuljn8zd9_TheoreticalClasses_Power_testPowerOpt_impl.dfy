method powerOpt(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  if n == 0 {
    p := 1.0;
  } else if n % 2 == 0 {
    var half := powerOpt(x, n / 2);
    /* code modified by LLM (iteration 1): Added lemma call to prove even case equivalence */
    powerEvenLemma(x, n);
    p := half * half;
  } else {
    var prev := powerOpt(x, n - 1);
    p := x * prev;
  }
}

//IMPL

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
  if n == 0 then 1.0 else x * power(x, n-1)
}

/* code modified by LLM (iteration 1): Added helper lemma to prove power equivalence for even exponents */
lemma powerEvenLemma(x: real, n: nat)
  requires n % 2 == 0 && n > 0
  ensures power(x, n) == power(x, n / 2) * power(x, n / 2)
{
  if n == 2 {
    // Base case: power(x, 2) == power(x, 1) * power(x, 1) == x * x
  } else {
    // Inductive case
    var half := n / 2;
    assert n == half + half;
    powerAddLemma(x, half, half);
  }
}

/* code modified by LLM (iteration 1): Added helper lemma to prove power addition property */
lemma powerAddLemma(x: real, m: nat, n: nat)
  ensures power(x, m + n) == power(x, m) * power(x, n)
{
  if m == 0 {
    // Base case: power(x, 0 + n) == 1.0 * power(x, n) == power(x, n)
  } else {
    // Inductive case: power(x, m + n) == x * power(x, (m-1) + n) == x * power(x, m-1) * power(x, n) == power(x, m) * power(x, n)
    powerAddLemma(x, m - 1, n);
  }
}

//IMPL testPowerOpt

/* code modified by LLM (iteration 1): Added test cases for powerOpt method */
method testPowerOpt(){
  var result1 := powerOpt(2.0, 3);
  var result2 := powerOpt(5.0, 0);
  var result3 := powerOpt(1.5, 2);
}