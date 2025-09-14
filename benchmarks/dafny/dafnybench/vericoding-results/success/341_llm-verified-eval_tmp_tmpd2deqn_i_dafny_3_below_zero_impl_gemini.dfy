// <vc-preamble>
function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{
    if |s| == 0 || n == 0 then
        0
    else
        s[0] + sum(s[1..], n-1)
}
// </vc-preamble>

// <vc-helpers>
lemma SumStepProperty(s: seq<int>, n: nat)
    requires n < |s|
    ensures sum(s, n + 1) == sum(s, n) + s[n]
    decreases n
{
    if n > 0 {
        SumStepProperty(s[1..], n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
  result := false;
  var current_sum: int := 0;
  var i: nat := 0;
  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant current_sum == sum(ops, i)
    invariant forall k: nat :: k <= i ==> sum(ops, k) >= 0
  {
    SumStepProperty(ops, i);
    current_sum := current_sum + ops[i];
    if current_sum < 0 {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
