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
  var acc := 1;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant acc == special_factorial_rec(i - 1)
  {
    acc := acc * factorial(i);
    i := i + 1;
  }
  
  result := acc;
}
// </vc-code>

