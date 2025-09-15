// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)

    ensures |s| == |strange|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added loop invariants to prove postcondition */
  var reversed := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |reversed| == i
  {
    reversed := reversed + [s[|s|-1-i]];
    i := i + 1;
  }
  strange := reversed;
}
// </vc-code>
