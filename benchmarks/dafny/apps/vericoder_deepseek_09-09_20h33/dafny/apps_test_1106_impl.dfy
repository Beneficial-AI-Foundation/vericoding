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
lemma dfs_result_leaf(i: int, n: int, a: seq<int>)
    requires 1 <= n <= 10
    requires 1 <= i < power2(n+1)
    requires |a| == power2(n+1)
    requires forall j :: 2 <= j < |a| ==> 1 <= a[j] <= 100
    requires a[0] == 0 && a[1] == 0
    requires i >= power2(n)
    ensures dfs_result(i, n, a) == (0, 0)
{
}

lemma dfs_result_inner(i: int, n: int, a: seq<int>)
    requires 1 <= n <= 10
    requires 1 <= i < power2(n)
    requires |a| == power2(n+1)
    requires forall j :: 2 <= j < |a| ==> 1 <= a[j] <= 100
    requires a[0] == 0 && a[1] == 0
    ensures dfs_result(i, n, a) == (
        if dfs_result(i * 2, n, a).1 + a[i * 2] < dfs_result(i * 2 + 1, n, a).1 + a[i * 2 + 1]
        then (dfs_result(i * 2, n, a).0 + dfs_result(i * 2 + 1, n, a).0 + 
              dfs_result(i * 2 + 1, n, a).1 + a[i * 2 + 1] - 
              dfs_result(i * 2, n, a).1 - a[i * 2],
              dfs_result(i * 2 + 1, n, a).1 + a[i * 2 + 1])
        else (dfs_result(i * 2, n, a).0 + dfs_result(i * 2 + 1, n, a).0 + 
              dfs_result(i * 2, n, a).1 + a[i * 2] - 
              dfs_result(i * 2 + 1, n, a).1 - a[i * 2 + 1],
              dfs_result(i * 2, n, a).1 + a[i * 2])
    )
{
}

lemma power2_properties(n: int)
    requires 0 <= n <= 11
    ensures power2(n) > 0
    decreases n
{
    if n > 0 {
        power2_properties(n-1);
    }
}

lemma array_to_seq_conversion(a: array<int>, size: int)
    requires a != null
    requires 0 <= size <= a.Length
    ensures a[..size] == seq(j | 0 <= j < size :: a[j])
{
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
    var size := power2(n+1);
    var a := new int[size];
    a[0] := 0;
    a[1] := 0;
    
    var i := 2;
    while i < size
        invariant 2 <= i <= size
        invariant forall j :: 2 <= j < i ==> a[j] == lights[j-2]
        invariant forall j :: i <= j < size ==> a[j] == 0
    {
        a[i] := lights[i-2];
        i := i + 1;
    }
    
    power2_properties(n+1);
    
    var stack := new (int, int)[size];
    var sp := 0;
    
    i := size - 1;
    while i >= 1
        invariant 0 <= i < size
        invariant sp == size - i - 1
        invariant forall j :: 0 <= j < sp ==> 
            stack[j].0 == dfs_result(i + j + 1, n, a[..])^0 && 
            stack[j].1 == dfs_result(i + j + 1, n, a[..])^1
        decreases i
    {
        array_to_seq_conversion(a, size);
        
        if i >= power2(n) {
            dfs_result_leaf(i, n, a[..]);
            stack[sp] := (0, 0);
            sp := sp + 1;
        } else {
            var left := stack[sp-2];
            var right := stack[sp-1];
            sp := sp - 2;
            
            var x1 := left.0; var m1 := left.1;
            var x2 := right.0; var m2 := right.1;
            
            dfs_result_inner(i, n, a[..]);
            var left_res := dfs_result(i * 2, n, a[..]);
            var right_res := dfs_result(i * 2 + 1, n, a[..]);
            
            if m1 + a[i * 2] < m2 + a[i * 2 + 1] {
                stack[sp] := (x1 + x2 + m2 + a[i * 2 + 1] - m1 - a[i * 2], m2 + a[i * 2 + 1]);
            } else {
                stack[sp] := (x1 + x2 + m1 + a[i * 2] - m2 - a[i * 2 + 1], m1 + a[i * 2]);
            }
            sp := sp + 1;
        }
        i := i - 1;
    }
    
    result := stack[0].0;
}
// </vc-code>

