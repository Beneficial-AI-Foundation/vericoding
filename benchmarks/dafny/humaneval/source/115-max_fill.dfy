method max_fill(grid: seq<seq<nat>>, capacity: nat) returns (cnt: nat)
  // pre-conditions-start
  requires capacity > 0
  requires forall i, j :: 0 <= i < |grid| && 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
  // pre-conditions-end
  // post-conditions-start
  ensures cnt == sum(gen_seq(grid, capacity, |grid|))
  // post-conditions-end
{
  // impl-start
  var i := 0;
  ghost var current := [];
  cnt := 0;
  while i < |grid|
    // invariants-start
    invariant 0 <= i <= |grid|
    invariant cnt == sum(current)
    invariant current == gen_seq(grid, capacity, i)
    // invariants-end
  {
    var j := 0;
    var sum_j: nat := 0;
    while j < |grid[i]|
      // invariants-start
      invariant 0 <= j <= |grid[i]|
      invariant sum_j == sum(grid[i][..j])
      // invariants-end
    {
      sum_j := sum_j + grid[i][j];
      // assert-start
      assert sum(grid[i][..j + 1]) == sum(grid[i][..j]) + grid[i][j] by {
        assert grid[i][..j+1][..j] == grid[i][..j];
        sum_prop(grid[i][..j + 1]);
      }
      // assert-end
      j := j + 1;
    }

    var current_el := (sum_j + capacity - 1) / capacity;
    // assert-start
    assert current_el == (sum(grid[i]) + capacity - 1) / capacity by {
      assert grid[i][..|grid[i]|] == grid[i];
    }
    // assert-end

    ghost var post_seq := gen_seq(grid, capacity, i + 1);
    current := current + [current_el];

    // assert-start
    assert current == post_seq by {
      assert post_seq[i] == current_el;
    }
    // assert-end

    // assert-start
    assert sum(current[..i + 1]) == sum(current[..i]) + current[i] by {
      assert current[..i+1][..i] == current[..i];
      sum_prop(current[..i + 1]);
    }
    // assert-end

    assert current == current[..i + 1]; // assert-line

    i := i + 1;
    cnt := cnt + current_el;
  }
  // impl-end
}

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
lemma sum_prop(s: seq<int>)
    requires |s| > 0
    ensures sum(s) == sum(s[..|s| - 1]) + s[ |s| - 1 ]
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}
// pure-end
