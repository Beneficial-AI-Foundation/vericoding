// ATOM 
function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
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
        while n != a.Length
            invariant 1 <= n <= a.Length
            invariant forall i :: 0 <= i < n ==> a[i] <= m
            invariant exists i :: 0 <= i < n && m == a[i]
        {
            if m < a[n] {
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
    while m != a.Length0
        invariant 0 <= m <= a.Length0
        invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
        invariant forall i, j :: m <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j])
    {
        var n := 0;
        while n != a.Length1
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

//IMPL CopyMatrix
method CopyMatrix(src: array2<int>, dst: array2<int>)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == src[i,j] 
{
    var m := 0;
    while m != src.Length0
        invariant 0 <= m <= src.Length0
        invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == src[i,j]
    {
        var n := 0;
        while n != src.Length1
            invariant 0 <= n <= src.Length1
            invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == src[i,j]
            invariant forall j :: 0 <= j < n ==> dst[m,j] == src[m,j]
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
    ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * src[i]
{
    var n := 0;
    while n != src.Length
        invariant 0 <= n <= src.Length
        invariant forall i :: 0 <= i < n ==> dst[i] == 2 * src[i]
    {
        dst[n] := 2 * src[n]; 
        n := n + 1;
    }
}

//IMPL RotateLeft
method RotateLeft(a: array<int>)
    requires a.Length > 0
    modifies a
    ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[i+1]) 
    ensures a[a.Length -1] == old(a[0])
{
    /* code modified by LLM (iteration 1): Added ghost variable to track original array values */
    ghost var original := a[..];
    var temp := a[0];
    var n := 0;
    while n != a.Length - 1
        invariant 0 <= n <= a.Length - 1
        invariant forall i :: 0 <= i < n ==> a[i] == original[i+1]
        invariant forall i :: n < i < a.Length - 1 ==> a[i] == original[i]
        invariant a[a.Length - 1] == original[a.Length - 1]
        invariant temp == original[0]
        invariant original == old(a[..])
    {
        a[n] := a[n+1];
        n := n + 1; 
    }
    a[a.Length - 1] := temp;
}

//IMPL RotateRight
method RotateRight(a: array<int>)
    requires a.Length > 0
    modifies a
    ensures forall i :: 1 <= i < a.Length ==> a[i] == old(a[i-1]) 
    ensures a[0] == old(a[a.Length-1])
{
    /* code modified by LLM (iteration 1): Added ghost variable to track original array values */
    ghost var original := a[..];
    var temp := a[a.Length - 1];
    var n := a.Length - 1;
    while n != 0
        invariant 0 <= n < a.Length
        invariant forall i :: n < i < a.Length ==> a[i] == original[i-1]
        invariant forall i :: 0 < i <= n ==> a[i] == original[i]
        invariant a[0] == original[0]
        invariant temp == original[a.Length - 1]
        invariant original == old(a[..])
        decreases n
    {
        a[n] := a[n-1];
        n := n - 1; 
    }
    a[0] := temp;
}