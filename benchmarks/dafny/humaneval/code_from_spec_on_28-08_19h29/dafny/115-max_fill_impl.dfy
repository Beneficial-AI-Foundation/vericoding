// <vc-helpers>
function SumSeq(s: seq<int>): int {
  if |s| == 0 then 0 else s[0] + SumSeq(s[1..])
}

function GenerateSeq(grid: seq<seq<nat>>, capacity: nat, len: nat): seq<int>
  requires capacity > 0
  requires len <= |grid|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
{
  seq(len, j requires 0 <= j < len => (SumSeq(grid[j]) + capacity - 1) / capacity)
}

lemma SumSeqNonNegative(s: seq<int>)
  ensures SumSeq(s) >= 0
{
  if |s| == 0 {
  } else {
    SumSeqNonNegative(s[1..]);
  }
}

lemma GenerateSeqNonNegative(grid: seq<seq<nat>>, capacity: nat, len: nat)
  requires capacity > 0
  requires len <= |grid|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  ensures forall i :: 0 <= i < len ==> GenerateSeq(grid, capacity, len)[i] >= 0
{
  for i := 0 to len
    invariant forall j :: 0 <= j < i ==> GenerateSeq(grid, capacity, len)[j] >= 0
  {
    assert SumSeq(grid[i]) >= 0;
    assert (SumSeq(grid[i]) + capacity - 1) / capacity >= 0;
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def max_fill_count(grid : list[list[int]], capacity : int) -> int
You are given a rectangular grid of wells. Each row represents a single well, and each 1 in a row represents a single unit of water. Each well has a corresponding bucket that can be used to extract water from it, and all buckets have the same capacity. Your task is to use the buckets to empty the wells. Output the number of times you need to lower the buckets. Constraints: * all wells have the same length * 1 <= grid.length <= 10^2 * 1 <= grid[:,1].length <= 10^2 * grid[i][j] -> 0 | 1 * 1 <= capacity <= 10
*/
// </vc-description>

// <vc-spec>
method max_fill_count(grid: seq<seq<nat>>, capacity: nat) returns (count: nat)
  requires capacity > 0
  requires 1 <= |grid| <= 100
  requires forall i :: 0 <= i < |grid| ==> 1 <= |grid[i]| <= 100
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  ensures count == SumSeq(GenerateSeq(grid, capacity, |grid|))
// </vc-spec>
// <vc-code>
{
  var total_count: nat := 0;
  var i: nat := 0;
  while i < |grid|
    invariant 0 <= i <= |grid|
    invariant total_count == SumSeq(GenerateSeq(grid, capacity, i))
  {
    var water_in_well := SumSeq(grid[i]);
    var buckets_needed := (water_in_well + capacity - 1) / capacity;
    total_count := total_count + buckets_needed;
    i := i + 1;
  }
  count := total_count;
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