// <vc-preamble>
/* Helper function to count occurrences of a target value in a sequence */
function CountOccurrences(xs: seq<int>, target: int): nat
{
    |set i | 0 <= i < |xs| && xs[i] == target|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): use |xs| for sequence length and prove occurrence positive */
lemma OccurrencePositive(xs: seq<int>, i: int)
  requires 0 <= i < |xs|
  ensures CountOccurrences(xs, xs[i]) > 0
{
  var S := set j | 0 <= j < |xs| && xs[j] == xs[i];
  assert i in S;
  assert CountOccurrences(xs, xs[i]) == |S|;
  assert |S| > 0;
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
  /* code modified by LLM (iteration 3): Implement MostFrequent using linear scan and CountOccurrences */
  var i := 1;
  var bestIdx := 0;
  var best := xs[0];
  var bestCount: nat := CountOccurrences(xs[..], best);
  while i < xs.Length
    decreases xs.Length - i
    invariant 0 <= i <= xs.Length
    invariant 0 <= bestIdx < i
    invariant xs[bestIdx] == best
    invariant bestCount == CountOccurrences(xs[..], best)
    invariant forall j :: 0 <= j < i ==> CountOccurrences(xs[..], xs[j]) <= bestCount
    invariant forall j :: 0 <= j < bestIdx ==> CountOccurrences(xs[..], xs[j]) < bestCount
  {
    var x := xs[i];
    var c := CountOccurrences(xs[..], x);
    if c > bestCount {
      best := x;
      bestCount := c;
      bestIdx := i;
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>
