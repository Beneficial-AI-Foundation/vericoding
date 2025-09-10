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
function compute_dfs(i: int, n: int, a: seq<int>): (res_x: int, res_m: int)
    requires 1 <= n <= 10
    requires 1 <= i < power2(n+1)
    requires |a| == power2(n+1)
    requires forall j :: 2 <= j < |a| ==> 1 <= a[j] <= 100
    requires a[0] == 0 && a[1] == 0
    decreases power2(n+1) - i
{
    if i >= power2(n) then (0, 0)
    else
        var left_x, left_m := compute_dfs(i * 2, n, a);
        var right_x, right_m := compute_dfs(i * 2 + 1, n, a);

        if left_m + a[i * 2] < right_m + a[i * 2 + 1] then
            (left_x + right_x + right_m + a[i * 2 + 1] - (left_m + a[i * 2]), right_m + a[i * 2 + 1])
        else
            (left_x + right_x + left_m + a[i * 2] - (right_m + a[i * 2 + 1]), left_m + a[i * 2])
}

lemma dfs_result_eq_compute_dfs(i: int, n: int, a: seq<int>)
    requires 1 <= n <= 10
    requires 1 <= i < power2(n+1)
    requires |a| == power2(n+1)
    requires forall j :: 2 <= j < |a| ==> 1 <= a[j] <= 100
    requires a[0] == 0 && a[1] == 0
    ensures dfs_result(i, n, a) == compute_dfs(i, n, a)
    decreases power2(n+1) - i
{
    if i >= power2(n) then
        assert dfs_result(i, n, a) == (0, 0);
        assert compute_dfs(i, n, a) == (0, 0);
    else
        dfs_result_eq_compute_dfs(i * 2, n, a);
        dfs_result_eq_compute_dfs(i * 2 + 1, n, a);
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
    var a: seq<int> := [0, 0] + lights;
    var x, m := compute_dfs(1, n, a);
    dfs_result_eq_compute_dfs(1, n, a);
    result := x;
}
// </vc-code>

