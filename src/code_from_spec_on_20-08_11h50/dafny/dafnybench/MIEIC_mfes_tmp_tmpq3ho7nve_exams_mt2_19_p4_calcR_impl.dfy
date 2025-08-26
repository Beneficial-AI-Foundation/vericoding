// <vc-spec>
function R(n: nat): nat {
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

// <vc-helpers>
// </vc-helpers>

method calcR(n: nat) returns (r: nat)
    ensures r == R(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    r := 0;
  } else {
    var i := 1;
    r := 0;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant r == R(i - 1)
    {
      if r > i {
        r := r - i;
      } else {
        r := r + i;
      }
      i := i + 1;
    }
  }
}
// </vc-code>