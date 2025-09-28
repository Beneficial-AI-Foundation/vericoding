// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function isCompositeWitness(n: nat, k: nat): bool {
  2 <= k && k < n && n % k == 0
}
// </vc-helpers>

// <vc-spec>
method IsPrime(n: nat) returns (result: bool)
    requires n >= 2
    ensures result ==> forall k: nat :: 2 <= k < n ==> n % k != 0
    ensures !result ==> exists k: nat :: 2 <= k < n && n % k == 0
// </vc-spec>
// <vc-code>
{
  var k: nat := 2;
  var hasDiv: bool := false;
  var wit: nat := 0;
  while k < n
    invariant 2 <= k <= n
    invariant !hasDiv ==> forall d: nat :: 2 <= d < k ==> n % d != 0
    invariant hasDiv ==> 2 <= wit < k && n % wit == 0
    decreases n - k
  {
    if isCompositeWitness(n, k) {
      wit := k;
      k := k + 1;
      hasDiv := true;
    } else {
      k := k + 1;
    }
  }
  result := !hasDiv;
}
// </vc-code>
