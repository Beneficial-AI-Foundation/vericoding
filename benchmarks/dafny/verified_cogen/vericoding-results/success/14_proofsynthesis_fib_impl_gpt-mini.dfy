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
lemma FiboMonotone(k: int, n: int) requires 0 <= k <= n ensures Fibo(k) <= Fibo(n) decreases n {
  if k == n {
    // trivial
  } else if n == 0 {
    // impossible unless k == 0 handled above
  } else if n == 1 {
    // then k == 0
    assert Fibo(0) == 0;
    assert Fibo(1) == 1;
    assert Fibo(0) <= Fibo(1);
  } else {
    // n >= 2 and k < n
    FiboMonotone(k, n - 1);
    assert Fibo(n) == Fibo(n - 1) + Fibo(n - 2);
    assert Fibo(n - 1) <= Fibo(n - 1) + Fibo(n - 2);
    assert Fibo(k) <= Fibo(n);
  }
}

lemma FiboFitsAll(n: int) requires n >= 0 && FiboFitsI32(n) ensures forall k :: 0 <= k <= n ==> Fibo(k) < 0x8000_0000 decreases n {
  if n == 0 {
    assert Fibo(0) < 0x8000_0000;
  } else {
    // Prove Fibo(n-1) < bound so we can apply the inductive lemma
    FiboMonotone(n - 1, n);
    assert Fibo(n - 1) <= Fibo(n);
    assert Fibo(n) < 0x8000_0000;
    assert Fibo(n - 1) < 0x8000_0000;
    FiboFitsAll(n - 1);
    // For k == n the property holds by the precondition FiboFitsI32(n)
  }
}
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
  a[0] := 0;
  a[1] := 1;
  var i := 2;
  while i < n
    invariant 0 <= i <= n && (forall k :: 0 <= k < i ==> a[k] == Fibo(k))
    decreases n - i
  {
    a[i] := a[i - 1] + a[i - 2];
    // By the invariant a[i-1] == Fibo(i-1) and a[i-2] == Fibo(i-2),
    // and by the definition of Fibo we have Fibo(i) == Fibo(i-1) + Fibo(i-2),
    // so a[i] == Fibo(i) holds after the assignment.
    i := i + 1;
  }
  ret := a[..];
}
// </vc-code>
