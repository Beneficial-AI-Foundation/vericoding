// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var low := 0;
  var high := xs.Length;
  
  while low < high
    invariant 0 <= low <= high <= xs.Length
    invariant forall i :: 0 <= i < low ==> xs[i] < target
    invariant forall i :: high <= i < xs.Length ==> target <= xs[i]
  {
    var mid := (low + high) / 2;
    if xs[mid] < target {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  result := low;
}
// </vc-code>
