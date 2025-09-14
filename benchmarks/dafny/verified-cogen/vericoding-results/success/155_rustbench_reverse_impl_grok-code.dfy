// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method reverse(a: array<int>) returns (result: seq<int>)
    ensures
        |result| == a.Length &&
        forall i :: 0 <= i < |result| ==> result[i] == a[a.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added loop invariants and decreases clause to prove postconditions */
  result := [];
  var i := a.Length - 1;
  while i >= 0
    invariant i >= -1
    invariant |result| == a.Length - 1 - i
    invariant forall j :: 0 <= j < |result| ==> result[j] == a[a.Length - 1 - j]
    decreases i
  {
    result := result + [a[i]];
    i := i - 1;
  }
}
// </vc-code>
