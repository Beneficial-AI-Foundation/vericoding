

// <vc-helpers>
function method sum_seq_nat(s: seq<nat>): nat
  reads s
{
  if |s| == 0 then 0 else s[0] + sum_seq_nat(s[1..])
}
// </vc-helpers>

// <vc-spec>
method max_fill(grid: seq<seq<nat>>, capacity: nat) returns (cnt: nat)
  // pre-conditions-start
  requires capacity > 0
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  // pre-conditions-end
  // post-conditions-start
  ensures cnt == sum(gen_seq(grid, capacity, |grid|))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var row_fills: seq<int> := [];
  for i := 0 to |grid| - 1
    invariant 0 <= i <= |grid|
    invariant |row_fills| == i
    invariant forall k | 0 <= k < i :: row_fills[k] == (sum_seq_nat(grid[k]) + capacity - 1) / capacity
  {
    var current_row_sum := sum_seq_nat(grid[i]);
    var fills := (current_row_sum + capacity - 1) / capacity;
    row_fills := row_fills + [fills];
  }
  cnt := sum(row_fills);
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