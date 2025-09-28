// <vc-preamble>
// Generate indices for a 1D grid of given size
// Returns a 2D array where the first dimension has size 1 and contains
// the indices [0, 1, 2, ..., n-1]
// </vc-preamble>

// <vc-helpers>

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
  var row: seq<nat> := [];
  var k: nat := 0;
  while k < n
    invariant k <= n
    invariant |row| == k
    invariant forall i :: 0 <= i < k ==> row[i] == i
    decreases n - k
  {
    row := row + [k];
    k := k + 1;
  }
  grid := [row];
}
// </vc-code>
