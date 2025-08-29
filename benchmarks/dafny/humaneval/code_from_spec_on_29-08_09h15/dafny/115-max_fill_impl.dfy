

// <vc-helpers>
lemma sum_non_negative(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures sum(s) >= 0
{
  if |s| == 0 {
  } else {
    sum_non_negative(s[1..]);
  }
}

lemma sum_empty()
  ensures sum([]) == 0
{
}

lemma sum_single(x: int)
  ensures sum([x]) == x
{
}

lemma sum_concat(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    sum_concat(s1[1..], s2);
    assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
  }
}

lemma sum_append(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
  sum_concat(s, [x]);
  sum_single(x);
}

lemma sum_slice_extend_by_one(s: seq<int>, j: nat)
  requires j < |s|
  ensures sum(s[..j+1]) == sum(s[..j]) + s[j]
{
  if j == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == [];
    sum_empty();
    sum_single(s[0]);
  } else {
    sum_slice_extend_by_one(s[1..], j-1);
    assert s[..j+1] == [s[0]] + s[1..][..j];
    assert s[..j] == [s[0]] + s[1..][..j-1];
  }
}

lemma gen_seq_property(grid: seq<seq<nat>>, capacity: nat, len: nat, i: nat)
  requires capacity > 0
  requires len <= |grid|
  requires i < len
  requires forall j, k :: 0 <= j < |grid| && 0 <= k < |grid[j]| ==> grid[j][k] == 0 || grid[j][k] == 1
  ensures gen_seq(grid, capacity, len)[i] == (sum(grid[i]) + capacity - 1) / capacity
{
}

lemma sum_of_binary_seq_non_negative(s: seq<nat>)
  requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
  ensures sum(s) >= 0
{
  if |s| == 0 {
  } else {
    sum_of_binary_seq_non_negative(s[1..]);
  }
}

lemma gen_seq_extend(grid: seq<seq<nat>>, capacity: nat, i: nat)
  requires capacity > 0
  requires i < |grid|
  requires forall j, k :: 0 <= j < |grid| && 0 <= k < |grid[j]| ==> grid[j][k] == 0 || grid[j][k] == 1
  ensures gen_seq(grid, capacity, i + 1) == gen_seq(grid, capacity, i) + [gen_seq(grid, capacity, i + 1)[i]]
{
}

lemma buckets_needed_non_negative(water: int, capacity: nat)
  requires capacity > 0
  requires water >= 0
  ensures (water + capacity - 1) / capacity >= 0
{
}

lemma sum_slice_complete(s: seq<nat>)
  ensures sum(s[..|s|]) == sum(s)
{
  assert s[..|s|] == s;
}

lemma sum_slice_extend(s: seq<nat>, j: nat)
  requires j <= |s|
  ensures sum(s[..j]) >= 0
{
  sum_non_negative(s[..j]);
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def max_fill_count(grid : list[list[int]], capacity : int) -> int
You are given a rectangular grid of wells. Each row represents a single well, and each 1 in a row represents a single unit of water. Each well has a corresponding bucket that can be used to extract water from it, and all buckets have the same capacity. Your task is to use the buckets to empty the wells. Output the number of times you need to lower the buckets. Constraints: * all wells have the same length * 1 <= grid.length <= 10^2 * 1 <= grid[:,1].length <= 10^2 * grid[i][j] -> 0 | 1 * 1 <= capacity <= 10
*/
// </vc-description>

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
    var water_in_well: int := 0;
    var j := 0;
    
    while j < |grid[i]|
      invariant 0 <= j <= |grid[i]|
      invariant water_in_well == sum(grid[i][..j])
    {
      sum_slice_extend_by_one(grid[i], j);
      water_in_well := water_in_well + grid[i][j];
      j := j + 1;
    }
    
    sum_slice_complete(grid[i]);
    assert water_in_well == sum(grid[i]);
    sum_of_binary_seq_non_negative(grid[i]);
    assert water_in_well >= 0;
    
    var buckets_needed := (water_in_well + capacity - 1) / capacity;
    buckets_needed_non_negative(water_in_well, capacity);
    
    assert buckets_needed == (sum(grid[i]) + capacity - 1) / capacity;
    gen_seq_property(grid, capacity, i + 1, i);
    assert gen_seq(grid, capacity, i + 1)[i] == buckets_needed;
    gen_seq_extend(grid, capacity, i);
    sum_append(gen_seq(grid, capacity, i), buckets_needed);
    
    cnt := cnt + buckets_needed;
    
    i := i + 1;
  }
  
  assert i == |grid|;
  assert cnt == sum(gen_seq(grid, capacity, |grid|));
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