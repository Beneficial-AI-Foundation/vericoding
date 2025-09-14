// <vc-preamble>
function R(n: nat): nat {
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method calcR(n: nat) returns (r: nat)
    ensures r == R(n)
// </vc-spec>
// <vc-code>
{
  r := 0;
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == R(i)
    decreases n - i
  {
    i := i + 1;
    if r > i {
      r := r - i;
    } else {
      r := r + i;
    }
  }
}
// </vc-code>
