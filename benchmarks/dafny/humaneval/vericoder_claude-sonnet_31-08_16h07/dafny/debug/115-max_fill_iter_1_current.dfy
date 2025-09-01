

// <vc-helpers>
lemma sum_non_negative(s: seq<nat>)
  ensures sum(s) >= 0
{
  if |s| == 0 {
  } else {
    sum_non_negative(s[1..]);
  }
}

lemma sum_preserves_type(s: seq<nat>) 
  ensures sum(s) >= 0
{
  sum_non_negative(s);
}

lemma gen_seq_bounds(grid: seq<seq<nat>>, capacity: nat, len: nat, i: nat)
  requires capacity > 0
  requires len <= |grid|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  requires i < len
  ensures (sum(grid[i]) + capacity - 1) / capacity >= 0
{
  sum_preserves_type(grid[i]);
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
  cnt := 0;
  var i := 0;
  while i < |grid|
    invariant 0 <= i <= |grid|
    invariant cnt == sum(gen_seq(grid, capacity, i))
  {
    gen_seq_bounds(grid, capacity, i + 1, i);
    var row_sum := sum(grid[i]);
    var buckets := (row_sum + capacity - 1) / capacity;
    cnt := cnt + buckets;
    i := i + 1;
  }
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