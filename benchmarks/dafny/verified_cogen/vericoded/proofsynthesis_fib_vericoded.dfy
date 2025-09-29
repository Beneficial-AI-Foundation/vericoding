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
  ret := [0, 1];
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant |ret| == i
    invariant forall j :: 0 <= j < i ==> ret[j] == Fibo(j)
    invariant i >= 2 ==> ret[i-1] == Fibo(i-1) && ret[i-2] == Fibo(i-2)
  {
    ret := ret + [ret[i-2] + ret[i-1]];
    i := i + 1;
  }
}
// </vc-code>
