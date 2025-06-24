// ATOM 
function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

//IMPL ComputePower
method ComputePower(N: int) returns (y: nat) 
    requires N >= 0
    ensures y == Power(N)
{
    y := 1;
    var x := 0; 
    while x != N
        decreases N - x
        invariant 0 <= x <= N
        invariant y == Power(x)
    {
        x, y := x + 1, y + y;
    }
}

//IMPL Max
method Max(a: array<nat>) returns (m: int)
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
    if a.Length == 0 {
        m := 0;
    } else {
        m := a[0];
        var n := 1;
        while n < a.Length
            invariant 1 <= n <= a.Length
            invariant forall i :: 0 <= i < n ==> a[i] <= m
            invariant exists i :: 0 <= i < n && m == a[i]
        {
            if a[n] > m {
                m := a[n];
            }
            n := n + 1;
        }
    }
}

//IMPL Cube
method Cube(n: nat) returns (c: nat) 
    ensures c == n * n * n
{
    c := n * n * n;
}

//IMPL IncrementMatrix
method IncrementMatrix(a: array2<int>)
    modifies a
    ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
    var m := 0;
    while m < a.Length0
        invariant 0 <= m <= a.Length0
        invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
        invariant forall i, j :: m <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j])
    {
        var n := 0;
        while n < a.Length1
            invariant 0 <= n <= a.Length1
            invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
            invariant forall j :: 0 <= j < n ==> a[m,j] == old(a[m,j]) + 1
            invariant forall j :: n <= j < a.Length1 ==> a[m,j] == old(a[m,j])
            invariant forall i, j :: m < i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j])
        {
            a[m,n] := a[m,n] + 1;
            n := n + 1;
        }
        m := m + 1;
    }
}