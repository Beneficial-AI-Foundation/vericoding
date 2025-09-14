

// <vc-helpers>
// Added a small lemma to reason about sequences of arrays, and to ensure
// the verifier sees a dereference of `a` in an `old(...)` context elsewhere if needed.
lemma SeqOldEquality<T>(a: array<T>)
  ensures a[..] == old(a[..])
{
  // This lemma is trivially true (seq of array in pre-state equals old seq),
  // and serves to give the verifier an occurrence of old(...) that
  // dereferences the heap (old(a[..])) to avoid the "old has no effect" warning.
}
// </vc-helpers>

// <vc-spec>
method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a == old(a)
ensures b.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> b[i] == a[a.Length - i - 1]
// </vc-spec>
// <vc-code>
{
  b := new char[a.Length];
  ghost var a0 := a[..];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> b[k] == a[a.Length - k - 1]
  {
    b[i] := a[a.Length - i - 1];
    i := i + 1;
  }
  assert a[..] == a0;
  return b;
}
// </vc-code>

