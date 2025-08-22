//IMPL
method BitwiseOr(a: array<int>, b: array<int>) returns (res: array<int>)
    requires a.Length == b.Length
    requires forall i ::  0 <= i < a.Length ==> 0 <= a[i] <= 65535 &&  0 <= b[i] <= 65535
    ensures res.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] as bv16 | b[i] as bv16) as int
{
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == (a[j] as bv16 | b[j] as bv16) as int
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        decreases a.Length - i
    {
        res[i] := (a[i] as bv16 | b[i] as bv16) as int;
        i := i + 1;
    }
}

//IMPL
method BitwiseOr' (a: array<bv32>, b: array<bv32>) returns (res: array<int>)
    requires a.Length == b.Length
    ensures res.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] | b[i]) as int
{
    res := new int[a.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == (a[j] | b[j]) as int
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        decreases a.Length - i
    {
        res[i] := (a[i] | b[i]) as int;
        i := i + 1;
    }
}