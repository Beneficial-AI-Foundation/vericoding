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
lemma dfs_result_bounds(i: int, n: int, a: seq<int>)
    requires 1 <= n <= 10
    requires 1 <= i < power2(n+1)
    requires |a| == power2(n+1)
    requires forall j :: 2 <= j < |a| ==> 1 <= a[j] <= 100
    requires a[0] == 0 && a[1] == 0
    ensures dfs_result(i, n, a).0 >= 0
    ensures dfs_result(i, n, a).1 >= 0
    decreases power2(n+1) - i
{
    if i >= power2(n) {
        // Base case
    } else {
        dfs_result_bounds(i * 2, n, a);
        dfs_result_bounds(i * 2 + 1, n, a);
    }
}

method dfs_iterative(i: int, n: int, a: seq<int>) returns (x: int, m: int)
    requires 1 <= n <= 10
    requires 1 <= i < power2(n+1)
    requires |a| == power2(n+1)
    requires forall j :: 2 <= j < |a| ==> 1 <= a[j] <= 100
    requires a[0] == 0 && a[1] == 0
    ensures (x, m) == dfs_result(i, n, a)
    ensures x >= 0 && m >= 0
    decreases power2(n+1) - i
{
    if i >= power2(n) {
        x := 0;
        m := 0;
    } else {
        var x1, m1 := dfs_iterative(i * 2, n, a);
        var x2, m2 := dfs_iterative(i * 2 + 1, n, a);
        
        if m1 + a[i * 2] < m2 + a[i * 2 + 1] {
            x := x1 + x2 + m2 + a[i * 2 + 1] - m1 - a[i * 2];
            m := m2 + a[i * 2 + 1];
        } else {
            x := x1 + x2 + m1 + a[i * 2] - m2 - a[i * 2 + 1];
            m := m1 + a[i * 2];
        }
        
        dfs_result_bounds(i * 2, n, a);
        dfs_result_bounds(i * 2 + 1, n, a);
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
    assert |a| == 2 + |lights| == 2 + (power2(n+1) - 2) == power2(n+1);
    assert forall j :: 2 <= j < |a| ==> 1 <= a[j] <= 100;
    
    var x, m := dfs_iterative(1, n, a);
    dfs_result_bounds(1, n, a);
    
    return x;
}
// </vc-code>

