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
/* helper modified by LLM (iteration 2): fixed non-decreasing decreases clause */
lemma SumNext(s: seq<int>, n: nat)
    requires n < |s|
    ensures sum(s, n + 1) == sum(s, n) + s[n]
    decreases n
{
    if n > 0 {
        SumNext(s[1..], n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method BelowZero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): no change in logic, fix was in helper */
  var current_sum: int := 0;
  var i: nat := 0;

  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant current_sum == sum(ops, i)
    invariant forall k: nat :: k < i ==> sum(ops, k) >= 0
  {
    if current_sum < 0 {
      result := true;
      return;
    }
    SumNext(ops, i);
    current_sum := current_sum + ops[i];
    i := i + 1;
  }

  if current_sum < 0 {
    result := true;
  } else {
    result := false;
  }
}
// </vc-code>
