function factorial(n: nat): nat
  decreases n
{
  if n == 0 then 1 else n * factorial(n - 1)
}
function special_factorial_rec(n: nat): nat
  decreases n
{
  if n == 0 then 1 else factorial(n) * special_factorial_rec(n - 1)
}

// <vc-helpers>
lemma special_factorial_rec_property(n: nat)
  requires n > 0
  ensures special_factorial_rec(n) == factorial(n) * special_factorial_rec(n - 1)
{
  // This follows directly from the definition of special_factorial_rec
}

lemma factorial_positive(n: nat)
  ensures factorial(n) > 0
{
  if n == 0 {
    // factorial(0) == 1 > 0
  } else {
    factorial_positive(n - 1);
    // factorial(n) == n * factorial(n - 1) and n > 0 and factorial(n - 1) > 0
  }
}

lemma special_factorial_rec_positive(n: nat)
  ensures special_factorial_rec(n) > 0
{
  if n == 0 {
    // special_factorial_rec(0) == 1 > 0
  } else {
    factorial_positive(n);
    special_factorial_rec_positive(n - 1);
    // special_factorial_rec(n) == factorial(n) * special_factorial_rec(n - 1)
    // and both factors are positive
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def special_factorial(n: int) -> int
The Brazilian factorial is defined as: brazilian_factorial(n) = n! * (n-1)! * (n-2)! * ... * 1! where n > 0. Please write a function that computes the Brazilian factorial.
*/
// </vc-description>

// <vc-spec>
method special_factorial(n: nat) returns (result: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result == special_factorial_rec(n)
  // post-conditions-end
// </vc-spec>

// <vc-code>
{
  result := 1;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant result == special_factorial_rec(i - 1)
    decreases n - i
  {
    var fact_i := 1;
    var j := 1;
    
    // Compute factorial(i)
    while j <= i
      invariant 1 <= j <= i + 1
      invariant fact_i == factorial(j - 1)
      decreases i - j
    {
      fact_i := fact_i * j;
      j := j + 1;
    }
    
    result := result * fact_i;
    i := i + 1;
  }
}
// </vc-code>

