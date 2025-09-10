function factorial(n: nat): nat
  decreases n
{
  if n == 0 then 1 else n * factorial(n - 1)
}
// pure-end
function special_factorial_rec(n: nat): nat
  decreases n
{
  if n == 0 then 1 else factorial(n) * special_factorial_rec(n - 1)
}
// pure-end
method special_factorial(n: nat) returns (result: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result == special_factorial_rec(n)
  // post-conditions-end
{
  // impl-start
  result := 1;
  var fact := 1;

  var i := 0;
  while i < n
    // invariants-start
    invariant 0 <= i <= n
    invariant result == special_factorial_rec(i)
    invariant fact == factorial(i)
    // invariants-end
    decreases n - i + 1
  {
    i := i + 1;
    fact := fact * i;
    result := result * fact;
  }
  // impl-end
}
