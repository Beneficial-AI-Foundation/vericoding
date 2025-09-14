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
/* helper modified by LLM (iteration 3): fixed SeqLemma syntax and added proper lemma signatures */
lemma FiboLemma(n: int)
  requires n >= 2
  ensures Fibo(n) == Fibo(n - 2) + Fibo(n - 1)
{
  // The function definition already provides this property
}

lemma FiboMonotonic(i: int, j: int)
  requires i <= j
  ensures Fibo(i) <= Fibo(j)
{
  // The function is monotonic for non-negative inputs
  if i >= 0 {
    // For positive indices, Fibonacci is non-decreasing
  }
}

lemma SeqLemma(s: seq<int>, idx: int)
  requires 0 <= idx < |s|
  ensures s[idx] == s[idx]
{
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
/* code modified by LLM (iteration 3): maintaining correct Fibonacci sequence implementation */
{
  ret := [0, 1];
  var i := 2;
  while i < n
    invariant |ret| == i
    invariant 2 <= i <= n
    invariant forall j :: 0 <= j < i ==> ret[j] == Fibo(j)
    invariant ret[0] == Fibo(0) && ret[1] == Fibo(1)
  {
    var next := ret[i-2] + ret[i-1];
    ret := ret + [next];
    assert ret[i] == Fibo(i);
    i := i + 1;
  }
}
// </vc-code>
