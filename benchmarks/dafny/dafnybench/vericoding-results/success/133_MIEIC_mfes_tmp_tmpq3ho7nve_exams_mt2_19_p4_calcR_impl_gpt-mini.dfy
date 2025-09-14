function R(n: nat): nat {
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method calcR(n: nat) returns (r: nat)
    ensures r == R(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    r := 0;
  } else {
    var rprev := calcR(n - 1);
    if rprev > n {
      r := rprev - n;
    } else {
      r := rprev + n;
    }
  }
}
// </vc-code>

