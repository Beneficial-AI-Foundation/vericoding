// <vc-helpers>
function sum_row(row: seq<nat>): nat
  requires forall j :: 0 <= j < |row| ==> row[j] == 0 || row[j] == 1
{
  if |row| == 0 then 0 else row[0] + sum_row(row[1..])
}

lemma SumRowEquivalent(row: seq<nat>)
  requires forall j :: 0 <= j < |row| ==> row[j] == 0 || row[j] == 1
  ensures sum_row(row) == sum(row)
{
  if |row| == 0 {
    assert sum_row(row) == 0;
    assert sum(row) == 0;
  } else {
    assert sum_row(row) == row[0] + sum_row(row[1..]);
    assert sum(row) == row[0] + sum(row[1..]);
    SumRowEquivalent(row[1..]);
  }
}

lemma SumGenSeq(grid: seq<seq<nat>>, capacity: nat, len: nat)
  requires capacity > 0
  requires len <= |grid|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  ensures sum(gen_seq(grid, capacity, len)) == sum(seq(len, j requires 0 <= j < len => (sum_row(grid[j]) + capacity - 1) / capacity))
{
  var s1 := gen_seq(grid, capacity, len);
  var s2 := seq(len, j requires 0 <= j < len => (sum_row(grid[j]) + capacity - 1) / capacity);
  assert |s1| == |s2|;
  forall i | 0 <= i < len
    ensures s1[i] == s2[i]
  {
    assert s1[i] == (sum(grid[i]) + capacity - 1) / capacity;
    SumRowEquivalent(grid[i]);
    assert sum_row(grid[i]) == sum(grid[i]);
    assert s2[i] == (sum_row(grid[i]) + capacity - 1) / capacity;
  }
  assert s1 == s2;
}

lemma SumRowPrefix(row: seq<nat>, k: nat)
  requires 0 <= k <= |row|
  requires forall j :: 0 <= j < |row| ==> row[j] == 0 || row[j] == 1
  ensures sum_row(row[..k]) == sum(row[..k])
{
  if k == 0 {
    assert row[..k] == [];
    assert sum_row([]) == 0;
    assert sum([]) == 0;
  } else {
    SumRowPrefix(row[1..], k-1);
    assert sum_row(row[..k]) == row[0] + sum_row(row[1..][..k-1]);
    assert sum(row[..k]) == row[0] + sum(row[1..][..k-1]);
  }
}

lemma SumSeqPrefix(grid: seq<seq<nat>>, capacity: nat, k: nat)
  requires 0 <= k <= |grid|
  requires capacity > 0
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  ensures sum(seq(k, j requires 0 <= j < k => (sum_row(grid[j]) + capacity - 1) / capacity)) == 
          sum(seq(k, j requires 0 <= j < k => (sum(grid[j]) + capacity - 1) / capacity))
{
  if k == 0 {
    assert seq(k, j requires 0 <= j < k => (sum_row(grid[j]) + capacity - 1) / capacity) == [];
    assert sum([]) == 0;
  } else {
    SumSeqPrefix(grid[1..], capacity, k-1);
    assert sum(seq(k, j requires 0 <= j < k => (sum_row(grid[j]) + capacity - 1) / capacity)) == 
           (sum_row(grid[0]) + capacity - 1) / capacity + 
           sum(seq(k-1, j requires 0 <= j < k-1 => (sum_row(grid[1..][j]) + capacity - 1) / capacity));
    SumRowEquivalent(grid[0]);
    assert sum_row(grid[0]) == sum(grid[0]);
  }
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
  var total: nat := 0;
  var i: nat := 0;
  while i < |grid|
    invariant 0 <= i <= |grid|
    invariant total == sum(seq(i, j requires 0 <= j < i => (sum_row(grid[j]) + capacity - 1) / capacity))
  {
    var row_sum: nat := 0;
    var j: nat := 0;
    while j < |grid[i]|
      invariant 0 <= j <= |grid[i]|
      invariant row_sum == sum_row(grid[i][..j])
    {
      row_sum := row_sum + grid[i][j];
      j := j + 1;
      assert row_sum == sum_row(grid[i][..j]);
    }
    SumRowEquivalent(grid[i]);
    assert row_sum == sum_row(grid[i]);
    var row_fill: nat := (row_sum + capacity - 1) / capacity;
    total := total + row_fill;
    i := i + 1;
  }
  SumGenSeq(grid, capacity, |grid|);
  cnt := total;
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