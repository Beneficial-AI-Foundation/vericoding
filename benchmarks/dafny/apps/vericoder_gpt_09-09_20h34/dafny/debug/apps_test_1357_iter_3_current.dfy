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
  var res := 0;
  var cur := 1;
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant m == |tasks|
    invariant 1 <= cur <= n
    invariant i == 0 ==> cur == 1
    invariant 0 < i ==> cur == tasks[i-1]
    invariant res >= 0
    invariant i == 0 ==> res == 0
    invariant i > 0 ==> res >= tasks[i-1] - 1
    invariant i > 0 ==> res <= (i - 1) * n + tasks[i-1] - 1
    decreases m - i
  {
    assert i < |tasks|;
    var t := tasks[i];
    var d := if t >= cur then t - cur else (n - cur) + t;

    // nonnegativity of d
    if t >= cur {
      assert d >= 0;
    } else {
      assert n - cur >= 0;
      assert 1 <= t;
      assert d >= 1;
      assert d >= 0;
    }

    // lower bound progress for next step
    if i == 0 {
      assert cur == 1;
      assert 1 <= t;
      assert t >= cur;
      assert d == t - cur;
      assert res == 0;
      assert res + d == t - 1;
    } else {
      assert cur == tasks[i-1];
      if t >= cur {
        assert res >= tasks[i-1] - 1;
        assert res + d >= tasks[i-1] - 1 + (t - cur);
        assert res + d >= t - 1;
      } else {
        assert res >= tasks[i-1] - 1;
        assert res + d >= tasks[i-1] - 1 + (n - cur + t);
        assert res + d >= n + t - 1;
        assert res + d >= t - 1;
      }
    }

    // upper bound progress for next step
    if i == 0 {
      assert res + d <= 0 * n + t - 1;
    } else {
      if t >= cur {
        assert res <= (i - 1) * n + tasks[i-1] - 1;
        assert res + d <= (i - 1) * n + tasks[i-1] - 1 + (t - cur);
        assert cur == tasks[i-1];
        assert res + d <= (i - 1) * n + t - 1;
      } else {
        assert res <= (i - 1) * n + tasks[i-1] - 1;
        assert res + d <= (i - 1) * n + tasks[i-1] - 1 + (n - cur + t);
        assert cur == tasks[i-1];
        assert res + d <= (i - 1) * n + tasks[i-1] - 1 + (n - tasks[i-1] + t);
        assert res + d <= i * n + t - 1;
      }
    }

    res := res + d;
    cur := t;
    assert 1 <= cur <= n;
    i := i + 1;
  }
  result := res;
}
// </vc-code>

