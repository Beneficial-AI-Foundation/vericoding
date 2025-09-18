// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): derive adjacent increasing from pairwise increasing */
lemma StrictlyIncreasing(xs: array<int>)
    requires forall i, j :: 0 <= i < j < xs.Length ==> xs[i] < xs[j]
    ensures forall i :: 0 <= i < xs.Length - 1 ==> xs[i] < xs[i+1]
{
    if xs.Length >= 2 {
        var i := 0;
        while i < xs.Length - 1
            invariant 0 <= i <= xs.Length - 1
            invariant forall k :: 0 <= k < i ==> xs[k] < xs[k+1]
            decreases xs.Length - 1 - i
        {
            assert 0 <= i < i+1 < xs.Length;
            assert xs[i] < xs[i+1];
            i := i + 1;
        }
    }
}

// </vc-helpers>

// <vc-spec>
method SearchInsert(xs: array<int>, target: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < xs.Length ==> xs[i] < xs[j]
    ensures 0 <= result <= xs.Length
    ensures forall i :: 0 <= i < result ==> xs[i] < target
    ensures result < xs.Length ==> target <= xs[result]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): binary search with invariants and lemma call */
  StrictlyIncreasing(xs);
  var low := 0;
  var high := xs.Length;
  while low < high
    invariant 0 <= low <= high <= xs.Length
    invariant forall i :: 0 <= i < low ==> xs[i] < target
    invariant forall j :: high <= j < xs.Length ==> target <= xs[j]
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    if xs[mid] < target {
      assert xs[mid] < target;
      assert forall i :: 0 <= i < mid ==> xs[i] < xs[mid];
      assert forall i :: 0 <= i < mid + 1 ==> xs[i] < target;
      low := mid + 1;
    } else {
      assert target <= xs[mid];
      assert forall j :: mid < j < xs.Length ==> xs[mid] < xs[j];
      assert forall j :: mid <= j < xs.Length ==> target <= xs[j];
      high := mid;
    }
  }
  result := low;
}
// </vc-code>
