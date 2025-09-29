predicate ValidInput(n: int, m: int, tasks: seq<int>)
{
    n >= 2 && m >= 1 && |tasks| == m && 
    forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
}

function MinTimeToComplete(n: int, tasks: seq<int>, currentPos: int, taskIndex: int): int
    requires n >= 2
    requires forall i :: 0 <= i < |tasks| ==> 1 <= tasks[i] <= n
    requires 1 <= currentPos <= n
    requires 0 <= taskIndex < |tasks|
{
    var target := tasks[taskIndex];
    if target >= currentPos then target - currentPos
    else (n - currentPos) + target
}

// <vc-helpers>
lemma TravelBounds(n: int, pos: int, target: int, t: int)
  requires n >= 2
  requires 1 <= pos <= n
  requires 1 <= target <= n
  requires t == (if target >= pos then target - pos else n - pos + target)
  ensures t >= target - pos
  ensures pos + t <= n + target
{
  if target >= pos {
    assert t == target - pos;
    assert t >= target - pos;
    assert pos + t == target;
    assert pos + t <= n + target;
  } else {
    assert t == n - pos + target;
    // n - pos >= 0 because pos <= n
    assert t >= target - pos;
    assert pos + t == n + target;
    assert pos + t <= n + target;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, tasks: seq<int>) returns (result: int)
    requires ValidInput(n, m, tasks)
    ensures result >= 0
    ensures m > 0 ==> result >= tasks[m-1] - 1
    ensures result <= (m - 1) * n + tasks[m-1] - 1
// </vc-spec>
// <vc-code>
{
  var pos := 1;
  result := 0;
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant 1 <= pos <= n
    invariant i == 0 ==> result == 0
    invariant i == 0 ==> pos == 1
    invariant i > 0 ==> pos == tasks[i-1]
    invariant i > 0 ==> result >= pos - 1
    invariant i > 0 ==> result <= (i-1)*n + pos - 1
  {
    var t: int;
    if tasks[i] >= pos {
      t := tasks[i] - pos;
    } else {
      t := n - pos + tasks[i];
    }

    TravelBounds(n, pos, tasks[i], t);

    if i == 0 {
      // initial case: result == 0 and pos == 1
      assert result == 0 && pos == 1;
      // travel from 1 to tasks[0] gives tasks[0]-1
      assert result + t == tasks[i] - 1;
      assert result + t <= i * n + tasks[i] - 1;
    } else {
      // i > 0 case: use invariants and TravelBounds to establish required inequalities
      assert result >= pos - 1;
      assert result <= (i - 1) * n + pos - 1;
      assert t >= tasks[i] - pos;
      assert result + t >= tasks[i] - 1;
      assert pos + t <= n + tasks[i];
      assert result + t <= (i - 1) * n + pos - 1 + t;
      assert (i - 1) * n + pos - 1 + t <= i * n + tasks[i] - 1;
      assert result + t <= i * n + tasks[i] - 1;
    }

    result := result + t;
    pos := tasks[i];
    i := i + 1;
  }
}
// </vc-code>

