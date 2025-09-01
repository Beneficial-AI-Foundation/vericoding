

// <vc-helpers>
lemma bucket_sum_lemma(s: seq<nat>, capacity: nat)
  requires capacity > 0
  requires forall x :: x in s ==> x == 0 || x == 1
  ensures (sum(s) + capacity - 1) / capacity == (if sum(s) == 0 then 0 else (sum(s) - 1) / capacity + 1)
{
  if |s| == 0 {
    assert sum(s) == 0;
  } else {
    bucket_sum_lemma(s[1..], capacity);
  }
}

lemma gen_seq_properties(grid: seq<seq<nat>>, capacity: nat, len: nat)
  requires capacity > 0
  requires len <= |grid|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  ensures forall j :: 0 <= j < len ==> gen_seq(grid, capacity, len)[j] == (sum(grid[j]) + capacity - 1) / capacity
{
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
    invariant i <= |grid|
    invariant cnt == sum(gen_seq(grid, capacity, i))
  {
    var row_sum := 0;
    var j := 0;
    while j < |grid[i]|
      invariant j <= |grid[i]|
      invariant row_sum == sum(grid[i][0..j])
    {
      row_sum := row_sum + grid[i][j];
      j := j + 1;
    }
    bucket_sum_lemma(grid[i], capacity);
    cnt := cnt + ((row_sum + capacity - 1) / capacity);
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