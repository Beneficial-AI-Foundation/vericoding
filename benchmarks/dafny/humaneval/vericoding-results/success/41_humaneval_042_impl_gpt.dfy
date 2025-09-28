// <vc-preamble>

predicate ValidInput(l: seq<int>)
{
    true
}

predicate CorrectOutput(l: seq<int>, result: seq<int>)
{
    |result| == |l| && 
    forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple increment function (unused) */
function Inc(x: int): int {
  x + 1
}
// </vc-helpers>

// <vc-spec>
method incr_list(l: seq<int>) returns (result: seq<int>)
    requires ValidInput(l)
    ensures CorrectOutput(l, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): build result via array then convert to sequence */
  var n := |l|;
  var a := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a.Length == n
    invariant n == |l|
    invariant forall j :: 0 <= j < i ==> a[j] == l[j] + 1
  {
    a[i] := l[i] + 1;
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
