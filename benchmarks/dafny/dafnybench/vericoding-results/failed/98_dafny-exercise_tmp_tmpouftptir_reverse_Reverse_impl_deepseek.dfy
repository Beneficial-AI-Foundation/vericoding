

// <vc-helpers>
lemma ReverseLemma(a: array<char>, b: array<char>, i: int, j: int)
  requires a != null && b != null
  requires b.Length == a.Length
  requires 0 <= i <= j < a.Length
  ensures forall k :: i <= k <= j ==> b[k] == a[a.Length - k - 1]
{
  // This lemma can be used to help prove properties about the reverse operation
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
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant b.Length == a.Length
    invariant forall j :: 0 <= j < i ==> b[j] == a[a.Length - j - 1]
  {
    b[i] := a[a.Length - i - 1];
    i := i + 1;
  }
  assert forall k :: 0 <= k < a.Length ==> b[k] == a[a.Length - k - 1];
}
// </vc-code>

