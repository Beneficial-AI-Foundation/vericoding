// <vc-preamble>
/* Helper function to count occurrences of a target value in a sequence */
function CountOccurrences(xs: seq<int>, target: int): nat
{
    |set i | 0 <= i < |xs| && xs[i] == target|
}
// </vc-preamble>

// <vc-helpers>
function CountAtIndex(xs: seq<int>, i: int): nat
  requires 0 <= i < |xs|
{
  CountOccurrences(xs, xs[i])
}
// </vc-helpers>

// <vc-spec>
method MostFrequent(xs: array<int>) returns (result: int)
    requires xs.Length > 0
    ensures result in xs[..]
    ensures forall x :: x in xs[..] ==> CountOccurrences(xs[..], x) <= CountOccurrences(xs[..], result)
    ensures exists first_idx :: 
        0 <= first_idx < xs.Length && 
        xs[first_idx] == result && 
        CountOccurrences(xs[..], result) == CountOccurrences(xs[..], xs[first_idx]) &&
        forall i :: 0 <= i < first_idx ==> CountOccurrences(xs[..], xs[i]) < CountOccurrences(xs[..], result)
// </vc-spec>
// <vc-code>
{
  var n := xs.Length;
  var bestIdx := 0;
  var bestCount := CountOccurrences(xs[..], xs[0]);
  var i := 1;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= bestIdx < n
    invariant bestCount == CountOccurrences(xs[..], xs[bestIdx])
    invariant forall j :: 0 <= j < i ==> CountOccurrences(xs[..], xs[j]) <= bestCount
    invariant forall j :: 0 <= j < bestIdx ==> CountOccurrences(xs[..], xs[j]) < bestCount
  {
    var c := CountOccurrences(xs[..], xs[i]);
    if c > bestCount {
      bestIdx := i;
      bestCount := c;
    }
    i := i + 1;
  }
  result := xs[bestIdx];
}
// </vc-code>
