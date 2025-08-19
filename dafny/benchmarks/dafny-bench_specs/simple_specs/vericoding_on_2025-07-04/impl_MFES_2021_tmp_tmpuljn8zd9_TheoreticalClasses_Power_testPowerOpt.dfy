//ATOM
// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
 ensures p == power(x, n)
{
  /* code modified by LLM (iteration 2): Added proof annotations and lemma calls to verify correctness */
  if n == 0 {
    p := 1.0;
  } else if n == 1 {
    p := x;
  } else if n % 2 == 0 {
    var half := powerOpt(x, n / 2);
    p := half * half;
    /* code modified by LLM (iteration 2): Call lemma to prove even case correctness */
    powerSquareLemma(x, n / 2);
  } else {
    var half := powerOpt(x, n / 2);
    p := x * half * half;
    /* code modified by LLM (iteration 2): Call lemma to prove odd case correctness */
    powerSquareLemma(x, n / 2);
  }
}

/* code modified by LLM (iteration 2): Added helper lemma to prove power(x, 2*k) == power(x, k) * power(x, k) */
lemma powerSquareLemma(x: real, k: nat)
  ensures power(x, 2 * k) == power(x, k) * power(x, k)
{
  if k == 0 {
    // Base case: power(x, 0) == 1.0
  } else {
    // Inductive case
    calc {
      power(x, 2 * k);
    ==
      x * power(x, 2 * k - 1);
    ==
      x * power(x, 2 * (k - 1) + 1);
    ==
      x * (x * power(x, 2 * (k - 1)));
    ==
      x * x * power(x, 2 * (k - 1));
    ==  { powerSquareLemma(x, k - 1); }
      x * x * power(x, k - 1) * power(x, k - 1);
    ==
      (x * power(x, k - 1)) * (x * power(x, k - 1));
    ==
      power(x, k) * power(x, k);
    }
  }
}

//ATOM
// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
  if n == 0 then 1.0 else x * power(x, n-1)
}

//ATOM
method testPowerOpt(){
  /* code modified by LLM (iteration 1): Added actual test cases to verify powerOpt works correctly */
  var result1 := powerOpt(2.0, 0);
  assert result1 == 1.0;
  
  var result2 := powerOpt(2.0, 1);
  assert result2 == 2.0;
  
  var result3 := powerOpt(2.0, 4);
  assert result3 == 16.0;
  
  var result4 := powerOpt(3.0, 3);
  assert result4 == 27.0;
}