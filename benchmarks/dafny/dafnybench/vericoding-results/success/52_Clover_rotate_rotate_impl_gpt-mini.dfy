

// <vc-helpers>
// No helpers required for this verification.
// </vc-helpers>

// <vc-spec>
method rotate(a: array<int>, offset:int) returns (b: array<int> )
  requires 0<=offset
  ensures b.Length==a.Length
  ensures forall  i::0<=i<a.Length ==>  b[i]==a[(i+offset)%a.Length]
// </vc-spec>
// <vc-code>
{
  if a.Length == 0 {
    b := new int[0];
    return;
  }
  var n := a.Length;
  b := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant b.Length == n
    invariant forall k :: 0 <= k < i ==> b[k] == a[(k + offset) % n]
  {
    b[i] := a[(i + offset) % n];
    i := i + 1;
  }
  return;
}
// </vc-code>

