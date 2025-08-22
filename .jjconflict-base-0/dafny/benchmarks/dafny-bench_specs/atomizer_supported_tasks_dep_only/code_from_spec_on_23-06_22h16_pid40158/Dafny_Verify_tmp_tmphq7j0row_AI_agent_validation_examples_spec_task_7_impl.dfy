// ATOM 
function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

//IMPL ComputePower1
method ComputePower1(N: int) returns (y: nat) 
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
        /* code modified by LLM (iteration 2): Changed y + y to 2 * y to match Power definition */
        x, y := x + 1, 2 * y;
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
            invariant forall i, j :: m + 1 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j])
        {
            a[m,n] := a[m,n] + 1;
            n := n + 1;
        }
        m := m + 1;
    }
}

//IMPL CopyMatrix
method CopyMatrix<T>(src: array2<T>, dst: array2<T>)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
    var m := 0;
    while m < src.Length0
        invariant 0 <= m <= src.Length0
        invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
    {
        var n := 0;
        while n < src.Length1
            invariant 0 <= n <= src.Length1
            invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
            invariant forall j :: 0 <= j < n ==> dst[m,j] == old(src[m,j])
        {
            dst[m,n] := src[m,n];
            n := n + 1;
        }
        m := m + 1;
    }
}

//IMPL DoubleArray
method DoubleArray(src: array<int>, dst: array<int>)
    requires src.Length == dst.Length
    modifies dst
    ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
    var n := 0;
    while n < src.Length
        invariant 0 <= n <= src.Length
        invariant forall i :: 0 <= i < n ==> dst[i] == 2 * old(src[i])
    {
        dst[n] := 2 * src[n];
        n := n + 1;
    }
}

//IMPL RotateLeft
method RotateLeft<T>(a: array<T>)
    requires a.Length > 0
    modifies a
    ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
    ensures a[a.Length -1] == old(a[0])
{
    /* code modified by LLM (iteration 2): Store the first element before any modifications */
    var temp := a[0];
    var n := 0;
    while n < a.Length - 1
        invariant 0 <= n <= a.Length - 1
        invariant forall i :: 0 <= i < n ==> a[i] == old(a[i+1])
        /* code modified by LLM (iteration 2): Fixed invariant to handle remaining elements correctly */
        invariant forall i :: n < i < a.Length - 1 ==> a[i] == old(a[i])
        invariant a[a.Length - 1] == old(a[a.Length - 1])
        invariant temp == old(a[0])
    {
        a[n] := a[n + 1];
        n := n + 1;
    }
    a[a.Length - 1] := temp;
}