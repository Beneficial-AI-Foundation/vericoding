// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method IsPrime(n: nat) returns (result: bool)
    requires n >= 2
    ensures result ==> forall k: nat :: 2 <= k < n ==> n % k != 0
    ensures !result ==> exists k: nat :: 2 <= k < n && n % k == 0
// </vc-spec>
// <vc-code>
{
  var d := 2;
  while d < n
    invariant 2 <= d <= n
    invariant forall k: nat :: 2 <= k < d ==> n % k != 0
    decreases n - d
  {
    if n % d == 0 {
      result := false;
      return;
    }
    d := d + 1;
  }
  result := true;
}
// </vc-code>
