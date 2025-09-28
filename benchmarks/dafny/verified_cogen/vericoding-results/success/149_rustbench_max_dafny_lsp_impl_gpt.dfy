// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsMaxIndex(a: array<int>, i: int) reads a {
  0 <= i < a.Length &&
  forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
}

predicate IsMaxIndexInPrefix(a: array<int>, i: int, m: int) reads a {
  0 <= i <= a.Length &&
  0 <= m < i &&
  forall k :: 0 <= k < i ==> a[k] <= a[m]
}

/* helper modified by LLM (iteration 2): removed reads clause from lemma to satisfy Dafny rules */
lemma PrefixMaxToGlobal(a: array<int>, m: int)
  requires IsMaxIndexInPrefix(a, a.Length, m)
  ensures IsMaxIndex(a, m)
{ }
// </vc-helpers>

// <vc-spec>
method MaxDafnyLsp(a: array<int>) returns (x: int)
    requires a.Length > 0
    ensures 0 <= x < a.Length
    ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[x]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented linear scan with loop invariants to find max index */
  var i := 1;
  var m := 0;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 0 <= m < i
    invariant forall k :: 0 <= k < i ==> a[k] <= a[m]
    decreases a.Length - i
  {
    if a[i] > a[m] {
      m := i;
    }
    i := i + 1;
  }
  x := m;
}
// </vc-code>
