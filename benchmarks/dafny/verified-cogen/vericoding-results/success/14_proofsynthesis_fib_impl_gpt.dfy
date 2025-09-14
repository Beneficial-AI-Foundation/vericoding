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
/* helper modified by LLM (iteration 2): basic lemmas about sequence append used by loop invariants */
lemma SeqAppendLen<T>(s: seq<T>, x: T)
  ensures |s + [x]| == |s| + 1
{ }

lemma SeqPreservePrefix<T>(s: seq<T>, x: T)
  ensures forall i :: 0 <= i < |s| ==> (s + [x])[i] == s[i]
{ }
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
  /* code modified by LLM (iteration 2): build Fibonacci sequence iteratively while maintaining invariants */
  var retSeq: seq<int> := [0, 1];
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant |retSeq| == i
    invariant forall j :: 2 <= j < i ==> retSeq[j] == Fibo(j)
    decreases n - i
  {
    retSeq := retSeq + [Fibo(i)];
    i := i + 1;
  }
  ret := retSeq;
}
// </vc-code>
