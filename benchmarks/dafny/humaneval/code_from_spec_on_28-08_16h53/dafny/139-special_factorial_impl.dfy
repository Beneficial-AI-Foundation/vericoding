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
lemma SpecialFactorialEquivalence(n: nat)
  ensures special_factorial(n) == special_factorial_rec(n)
{
  if n == 0 {
    // Base case: both return 1
  } else {
    // Inductive case: both compute factorial(n) * special_factorial(n-1)
    SpecialFactorialEquivalence(n - 1);
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
function special_factorial(n: nat): nat
  decreases n
  ensures n == 0 ==> special_factorial(n) == 1
  ensures n > 0 ==> special_factorial(n) == factorial(n) * special_factorial(n - 1)
// </vc-spec>
// <vc-code>
function special_factorial(n: nat): nat
  decreases n
  ensures n == 0 ==> special_factorial(n) == 1
  ensures n > 0 ==> special_factorial(n) == factorial(n) * special_factorial(n - 1)
{
  if n == 0 then 1 else factorial(n) * special_factorial(n - 1)
}
// </vc-code>
