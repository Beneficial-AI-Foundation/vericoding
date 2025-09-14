

// <vc-helpers>
lemma sum_gen_seq_append(grid: seq<seq<nat>>, capacity: nat, len: nat)
  requires capacity > 0
  requires len < |grid|
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  ensures sum(gen_seq(grid, capacity, len + 1)) == sum(gen_seq(grid, capacity, len)) + (sum(grid[len]) + capacity - 1) / capacity
{
  var s1 := gen_seq(grid, capacity, len);
  var s2 := gen_seq(grid, capacity, len + 1);
  
  assert s2 == s1 + [(sum(grid[len]) + capacity - 1) / capacity];
  
  calc {
    sum(s2);
    == sum(s1 + [(sum(grid[len]) + capacity - 1) / capacity]);
    == { sum_append(s1, [(sum(grid[len]) + capacity - 1) / capacity]); }
    sum(s1) + sum([(sum(grid[len]) + capacity - 1) / capacity]);
    == { assert sum([(sum(grid[len]) + capacity - 1) / capacity]) == (sum(grid[len]) + capacity - 1) / capacity; }
    sum(s1) + (sum(grid[len]) + capacity - 1) / capacity;
  }
}

lemma sum_append(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    calc {
      sum(s1 + s2);
      == { assert s1 + s2 == [s1[0]] + (s1[1..] + s2); }
      sum([s1[0]] + (s1[1..] + s2));
      == { assert sum([s1[0]] + (s1[1..] + s2)) == s1[0] + sum(s1[1..] + s2); }
      s1[0] + sum(s1[1..] + s2);
      == { sum_append(s1[1..], s2); }
      s1[0] + sum(s1[1..]) + sum(s2);
      == { assert sum(s1) == s1[0] + sum(s1[1..]); }
      sum(s1) + sum(s2);
    }
  }
}

lemma sum_append_single(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
  sum_append(s, [x]);
  assert sum([x]) == x;
}

lemma sum_nat_is_nat(s: seq<nat>)
  ensures sum(s) >= 0
{
  if |s| == 0 {
    assert sum(s) == 0;
  } else {
    sum_nat_is_nat(s[1..]);
    assert sum(s) == s[0] + sum(s[1..]);
    assert s[0] >= 0;
    assert sum(s[1..]) >= 0;
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
  cnt := 0;
  var i := 0;
  
  while i < |grid|
    invariant 0 <= i <= |grid|
    invariant cnt == sum(gen_seq(grid, capacity, i))
  {
    var row_sum: nat := 0;
    var j := 0;
    
    while j < |grid[i]|
      invariant 0 <= j <= |grid[i]|
      invariant row_sum == sum(grid[i][..j])
    {
      assert grid[i][..j+1] == grid[i][..j] + [grid[i][j]];
      sum_append_single(grid[i][..j], grid[i][j]);
      row_sum := row_sum + grid[i][j];
      j := j + 1;
    }
    
    assert grid[i][..|grid[i]|] == grid[i];
    assert row_sum == sum(grid[i]);
    
    sum_nat_is_nat(grid[i]);
    assert row_sum >= 0;
    var fills: nat := (row_sum + capacity - 1) / capacity;
    cnt := cnt + fills;
    
    sum_gen_seq_append(grid, capacity, i);
    i := i + 1;
  }
  
  assert i == |grid|;
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