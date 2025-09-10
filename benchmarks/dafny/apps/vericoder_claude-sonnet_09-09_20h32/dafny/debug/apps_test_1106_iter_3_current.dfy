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
lemma PowerMonotonic(n: int)
    requires n >= 0
    ensures power2(n) <= power2(n+1)
{
    if n == 0 {
        assert power2(0) == 1;
        assert power2(1) == 2;
    } else {
        PowerMonotonic(n-1);
        assert power2(n+1) == 2 * power2(n);
    }
}

lemma PowerBounds(n: int)
    requires 1 <= n <= 10
    ensures power2(n) <= power2(n+1) - 1
{
    PowerMonotonic(n);
    assert power2(n+1) == 2 * power2(n);
}

function dfs(i: int, n: int, a: seq<int>, memo_ref: map<int, (int, int)>): (int, int, map<int, (int, int)>)
    requires 1 <= n <= 10
    requires 1 <= i < power2(n+1)
    requires |a| == power2(n+1)
    requires forall j :: 2 <= j < |a| ==> 1 <= a[j] <= 100
    requires a[0] == 0 && a[1] == 0
    decreases power2(n+1) - i
{
    if i in memo_ref then
        (memo_ref[i].0, memo_ref[i].1, memo_ref)
    else if i >= power2(n) then
        var new_memo := memo_ref[i := (0, 0)];
        (0, 0, new_memo)
    else
        var (x1, m1, memo1) := dfs(i * 2, n, a, memo_ref);
        var (x2, m2, memo2) := dfs(i * 2 + 1, n, a, memo1);
        var res := if m1 + a[i * 2] < m2 + a[i * 2 + 1] then
            (x1 + x2 + m2 + a[i * 2 + 1] - m1 - a[i * 2], m2 + a[i * 2 + 1])
        else
            (x1 + x2 + m1 + a[i * 2] - m2 - a[i * 2 + 1], m1 + a[i * 2]);
        var final_memo := memo2[i := res];
        (res.0, res.1, final_memo)
}

lemma dfs_correctness(i: int, n: int, a: seq<int>, memo_ref: map<int, (int, int)>)
    requires 1 <= n <= 10
    requires 1 <= i < power2(n+1)
    requires |a| == power2(n+1)
    requires forall j :: 2 <= j < |a| ==> 1 <= a[j] <= 100
    requires a[0] == 0 && a[1] == 0
    ensures dfs(i, n, a, memo_ref).0 == dfs_result(i, n, a).0
    decreases power2(n+1) - i
{
    if i >= power2(n) {
        assert dfs_result(i, n, a) == (0, 0);
    } else {
        dfs_correctness(i * 2, n, a, memo_ref);
        var (x1, m1, memo1) := dfs(i * 2, n, a, memo_ref);
        dfs_correctness(i * 2 + 1, n, a, memo1);
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
    var memo: map<int, (int, int)> := map[];
    
    PowerBounds(n);
    dfs_correctness(1, n, a, memo);
    var (res_x, res_m, final_memo) := dfs(1, n, a, memo);
    result := res_x;
}
// </vc-code>

