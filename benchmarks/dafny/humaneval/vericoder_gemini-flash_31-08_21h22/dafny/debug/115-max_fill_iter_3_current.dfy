

// <vc-helpers>
function sum_nat(s: seq<nat>) : nat {
    if |s| == 0 then 0 else s[0] + sum_nat(s[1..])
}

// Helper function to sum a sequence of integers, ensuring the sum is non-negative
function sum_int(s: seq<int>): nat
  requires forall x :: x in s ==> x >= 0
{
  if |s| == 0 then 0 else s[0] + sum_int(s[1..])
}

// function gen_seq_sum(grid: seq<seq<nat>>, capacity: nat, k: nat): nat
//   requires capacity > 0
//   requires k <= |grid|
//   requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
// {
//   sum_int(seq(k, i requires 0 <= i < k => ((sum_nat(grid[i]) as int) + capacity - 1) / capacity))
// }
// Instead of sum_int on seq<int>, let's define a function that directly calculates the sum of the capacities.
// This avoids the use of `sum_int` where we need to constrain elements to be non-negative
// since `gen_seq` directly returns integers that are also non-negative as per its definition.
function current_capacity_sum(grid: seq<seq<nat>>, capacity: nat, k: nat): nat
  requires capacity > 0
  requires k <= |grid|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  ensures current_capacity_sum(grid, capacity, k) >= 0
{
  if k==0 then 0
  else current_capacity_sum(grid, capacity, k-1) + (sum_nat(grid[k-1]) + capacity - 1) / capacity
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
    var count: nat := 0;
    for i := 0 to |grid|
        invariant 0 <= i <= |grid|
        invariant count == current_capacity_sum(grid, capacity, i)
    {
        if i < |grid| {
            count := count + (sum_nat(grid[i]) + capacity - 1) / capacity;
        }
    }
    return count;
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