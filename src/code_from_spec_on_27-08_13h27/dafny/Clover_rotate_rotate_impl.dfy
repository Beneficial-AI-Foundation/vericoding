// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method rotate(a: array<int>, offset:int) returns (b: array<int> )
  requires 0<=offset
  ensures b.Length==a.Length
  ensures forall  i::0<=i<a.Length ==>  b[i]==a[(i+offset)%a.Length]
// </vc-spec>
// </vc-spec>

// <vc-code>
method RotateArray(a: array<int>, offset: int) returns (b: array<int>)
  requires 0 <= offset
  ensures b.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> b[i] == a[(i + offset) % a.Length]
{
  b := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> b[k] == a[(k + offset) % a.Length]
  {
    b[i] := a[(i + offset) % a.Length];
    i := i + 1;
  }
}
// </vc-code>
