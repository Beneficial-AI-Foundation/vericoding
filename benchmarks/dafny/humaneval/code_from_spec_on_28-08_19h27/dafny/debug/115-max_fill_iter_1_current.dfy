// <vc-helpers>
lemma SumNonNegative(s: seq<nat>)
  ensures sum(s) >= 0
{
  if |s| == 0 {
  } else {
    SumNonNegative(s[1..]);
  }
}

lemma SumBounds(s: seq<nat>)
  ensures sum(s) <= |s|
  requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
{
  if |s| == 0 {
  } else {
    SumBounds(s[1..]);
  }
}

lemma CeilDivisionBounds(n: nat, d: nat)
  requires d > 0
  ensures (n + d - 1) / d >= 0
  ensures n <= |seq(n, _ => 1)| ==> (n + d - 1) / d <= n
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def max_fill_count(grid : list[list[int]], capacity : int) -> int
You are given a rectangular grid of wells. Each row represents a single well, and each 1 in a row represents a single unit of water. Each well has a corresponding bucket that can be used to extract water from it, and all buckets have the same capacity. Your task is to use the buckets to empty the wells. Output the number of times you need to lower the buckets. Constraints: * all wells have the same length * 1 <= grid.length <= 10^2 * 1 <= grid[:,1].length <= 10^2 * grid[i][j] -> 0 | 1 * 1 <= capacity <= 10
*/
// </vc-description>

// <vc-spec>
method max_fill_count(grid: seq<seq<nat>>, capacity: nat) returns (result: nat)
  requires capacity > 0
  requires |grid| > 0
  requires forall i :: 0 <= i < |grid| ==> |grid[i]| == |grid[0]|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var total := 0;
  var i := 0;
  
  while i < |grid|
    invariant 0 <= i <= |grid|
    invariant total >= 0
  {
    SumNonNegative(grid[i]);
    SumBounds(grid[i]);
    var water_in_well := sum(grid[i]);
    var buckets_needed := (water_in_well + capacity - 1) / capacity;
    CeilDivisionBounds(water_in_well, capacity);
    total := total + buckets_needed;
    i := i + 1;
  }
  
  result := total;
}
// </vc-code>

function gen_seq(grid: seq<seq<nat>>, capacity: nat, len: nat): seq<int>
  requires capacity > 0
  requires len <= |grid|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
{
  seq(len, j requires 0 <= j < len => (sum(grid[j]) + capacity - 1) / capacity)
}
// pure-end
function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end