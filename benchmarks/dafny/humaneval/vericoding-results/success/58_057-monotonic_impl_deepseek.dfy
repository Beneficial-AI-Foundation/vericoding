// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fix helper functions to match postcondition specification */
function isIncreasing(xs: seq<int>): bool { forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j] }
function isDecreasing(xs: seq<int>): bool { forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j] }
// </vc-helpers>

// <vc-spec>
method monotonic(xs: seq<int>) returns (result: bool)

  requires |xs| > 0

  ensures result <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) || (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Return result based on fixed helper functions */
  result := isIncreasing(xs) || isDecreasing(xs);
}
// </vc-code>
