predicate ValidInput(n: int, lights: seq<int>)
{
    1 <= n <= 10 &&
    |lights| == power2(n+1) - 2 &&
    forall i :: 0 <= i < |lights| ==> 1 <= lights[i] <= 100
}

function power2(n: int): int
    requires n >= 0
    ensures power2(n) > 0
    ensures power2(n) == if n == 0 then 1 else 2 * power2(n-1)
{
    if n <= 0 then 1
    else 2 * power2(n - 1)
}

ghost function dfs_result(i: int, n: int, a: seq<int>): (int, int)
    requires 1 <= n <= 10
    requires 1 <= i < power2(n+1)
    requires |a| == power2(n+1)
    requires forall j :: 2 <= j < |a| ==> 1 <= a[j] <= 100
    requires a[0] == 0 && a[1] == 0
    decreases power2(n+1) - i
{
    if i >= power2(n) then (0, 0)
    else
        var left := dfs_result(i * 2, n, a);
        var right := dfs_result(i * 2 + 1, n, a);
        var x1 := left.0; var m1 := left.1;
        var x2 := right.0; var m2 := right.1;
        if m1 + a[i * 2] < m2 + a[i * 2 + 1] then
            (x1 + x2 + m2 + a[i * 2 + 1] - m1 - a[i * 2], m2 + a[i * 2 + 1])
        else
            (x1 + x2 + m1 + a[i * 2] - m2 - a[i * 2 + 1], m1 + a[i * 2])
}

// <vc-helpers>
method Compute(i: int, n: int, a: seq<int>) returns (x: int, m: int)
  requires 1 <= n <= 10
  requires 1 <= i < power2(n+1)
  requires |a| == power2(n+1)
  requires forall j :: 2 <= j < |a| ==> 1 <= a[j] <= 100
  requires a[0] == 0 && a[1] == 0
  ensures (x, m) == dfs_result(i, n, a)
  ensures x >= 0
  decreases power2(n+1) - i
{
  if i >= power2(n) {
    x := 0; m := 0;
  } else {
    assert power2(n+1) == 2 * power2(n);
    var l := i * 2;
    var r := i * 2 + 1;
    assert l < |a|;
    assert r < |a|;
    assert l >= 2;
    assert r >= 2;

    var x1:int; var m1:int;
    (x1, m1) := Compute(l, n, a);
    var x2:int; var m2:int;
    (x2, m2) := Compute(r, n, a);

    if m1 + a[l] < m2 + a[r] {
      x := x1 + x2 + m2 + a[r] - m1 - a[l];
      m := m2 + a[r];
      assert m2 + a[r] - m1 - a[l] > 0;
      assert x >= 0;
    } else {
      x := x1 + x2 + m1 + a[l] - m2 - a[r];
      m := m1 + a[l];
      assert m1 + a[l] - m2 - a[r] >= 0;
      assert x >= 0;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, lights: seq<int>) returns (result: int)
    requires ValidInput(n, lights)
    ensures result >= 0
    ensures result == dfs_result(1, n, [0, 0] + lights).0
// </vc-spec>
// <vc-code>
{
  var a := [0, 0] + lights;

  assert |a| == 2 + |lights|;
  assert |lights| == power2(n+1) - 2;
  assert 2 + (power2(n+1) - 2) == power2(n+1);
  assert |a| == power2(n+1);

  assert a[0] == 0 && a[1] == 0;

  assert forall j :: 2 <= j < |a| ==> 1 <= a[j] <= 100 by {
    forall j | 2 <= j < |a| {
      assert j >= 2;
      assert j - 2 >= 0;
      assert j - 2 < |lights|; 
      assert a[j] == lights[j - 2];
      assert 1 <= lights[j - 2] <= 100;
    }
  }

  assert power2(n+1) == 2 * power2(n);
  assert 1 < power2(n+1);

  var x:int; var m:int;
  (x, m) := Compute(1, n, a);
  result := x;
}
// </vc-code>

