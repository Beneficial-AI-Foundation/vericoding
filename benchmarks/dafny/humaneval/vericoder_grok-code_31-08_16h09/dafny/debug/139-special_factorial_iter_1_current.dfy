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
// No helpers needed for this implementation
// </vc-helpers>

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
  var prod: nat := 1;
  var i: nat := 1;
  while i <= n
    decreases n - i
    invariant 1 <= i <= n + 1
    invariant prod == special_factorial_rec(i - 1)
  {
    prod := prod * factorial(i);
    i := i + 1;
  }
  result := prod;
}
// </vc-code>

