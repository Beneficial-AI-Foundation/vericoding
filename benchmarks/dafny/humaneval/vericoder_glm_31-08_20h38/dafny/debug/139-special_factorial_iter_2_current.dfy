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
method factorial_method(n: nat) returns (r: nat)
  ensures r == factorial(n)
{
  r := 1;
  var i := 1;
  while i <= n 
    invariant 1 <= i <= n+1
    invariant r == factorial(i-1)
  {
    r := r * i;
    i := i + 1;
  }
}
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
var r := 1
for i := 1 to n 
    invariant 1 <= i <= n+1
    invariant r == special_factorial_rec(i-1)
{
    r := r * factorial_method(i);
}
return r
// </vc-code>

