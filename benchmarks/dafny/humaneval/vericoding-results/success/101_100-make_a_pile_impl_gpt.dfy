// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): provide step-of-two predicate and closed-form value function for pile construction */
predicate IsStepTwo(s: seq<int>) { forall i :: 1 <= i < |s| ==> s[i] == s[i - 1] + 2 }
function pileValue(n: int, i: nat): int { n + 2 * i }
// </vc-helpers>

// <vc-spec>
method make_a_pile(n: int) returns (pile: seq<int>)

  requires n >= 0

  ensures |pile| == n
  ensures forall i :: 1 <= i < n ==> pile[i] == pile[i - 1] + 2
  ensures n > 0 ==> pile[0] == n
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): constructive sequence build without assumes; maintains invariants to prove postconditions */
  var acc: seq<int> := [];
  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant |acc| == i
    invariant forall k :: 0 <= k < |acc| ==> acc[k] == n + 2 * k
    invariant forall k :: 1 <= k < |acc| ==> acc[k] == acc[k - 1] + 2
  {
    acc := acc + [n + 2 * i];
    i := i + 1;
  }
  pile := acc;
}
// </vc-code>
