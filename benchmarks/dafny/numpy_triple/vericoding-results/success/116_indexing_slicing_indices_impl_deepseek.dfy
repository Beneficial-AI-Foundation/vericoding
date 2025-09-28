// <vc-preamble>
// Generate indices for a 1D grid of given size
// Returns a 2D array where the first dimension has size 1 and contains
// the indices [0, 1, 2, ..., n-1]
// </vc-preamble>

// <vc-helpers>
function seqRange(start: nat, count: nat): seq<nat>
  decreases count
  ensures |seqRange(start, count)| == count
  ensures forall i :: 0 <= i < count ==> seqRange(start, count)[i] == start + i
{
  if count == 0 then []
  else [start] + seqRange(start + 1, count - 1)
}

lemma seqRangeProperties(start: nat, count: nat)
  requires count >= 0
  decreases count
  ensures |seqRange(start, count)| == count
  ensures forall i :: 0 <= i < count ==> seqRange(start, count)[i] == start + i
  ensures forall i, j :: 0 <= i < j < count ==> seqRange(start, count)[i] < seqRange(start, count)[j]
{
  if count > 0 {
    seqRangeProperties(start + 1, count - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method indices(n: nat) returns (grid: seq<seq<nat>>)
    // The output has exactly one row
    ensures |grid| == 1
    // The single row has exactly n elements
    ensures |grid[0]| == n
    // Each position i contains the value i
    ensures forall i :: 0 <= i < n ==> grid[0][i] == i
    // The indices are in ascending order
    ensures forall i, j :: 0 <= i < j < n ==> grid[0][i] < grid[0][j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Use seqRange helper function */
  var row: seq<nat> := seqRange(0, n);
  grid := [row];
}
// </vc-code>
