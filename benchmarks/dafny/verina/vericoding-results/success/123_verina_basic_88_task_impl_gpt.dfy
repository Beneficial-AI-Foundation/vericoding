// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers required for ToArray; section intentionally left blank */
// </vc-helpers>

// <vc-spec>
method ToArray(xs: seq<int>) returns (result: array<int>)
    ensures
        result.Length == |xs| &&
        forall i :: 0 <= i < |xs| ==> result[i] == xs[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): removed null invariant; added invariant linking n and |xs| and implemented copy loop */
  var n := |xs|;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant n == |xs|
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == xs[j]
  {
    result[i] := xs[i];
    i := i + 1;
  }
}
// </vc-code>
