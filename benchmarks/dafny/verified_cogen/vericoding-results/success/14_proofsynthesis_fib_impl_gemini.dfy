// <vc-preamble>
function Fibo(n: int): nat
    decreases n
{
    if n <= 0 then 0 else if n == 1 then 1
    else Fibo(n - 2) + Fibo(n - 1)
}

predicate FiboFitsI32(n: int) {
    Fibo(n) < 0x8000_0000
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Fibonacci(n: int) returns (ret: seq<int>)
    requires
        FiboFitsI32(n) &&
        n >= 2
    ensures
        |ret| == n &&
        (forall i :: 2 <= i < n ==> ret[i] == Fibo(i))
// </vc-spec>
// <vc-code>
{
    var a := new int[n];
    a[0] := Fibo(0);
    a[1] := Fibo(1);
    var i := 2;
    while i < n
        invariant 2 <= i <= n
        invariant forall j :: 0 <= j < i ==> a[j] == Fibo(j)
    {
        a[i] := a[i-1] + a[i-2];
        i := i + 1;
    }
    ret := a[..];
}
// </vc-code>
