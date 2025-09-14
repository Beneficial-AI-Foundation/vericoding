

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method rotate(a: array<int>, offset:int) returns (b: array<int> )
  requires 0<=offset
  ensures b.Length==a.Length
  ensures forall  i::0<=i<a.Length ==>  b[i]==a[(i+offset)%a.Length]
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  b := new int[n];
  for i := 0 to n
    invariant forall j :: 0<=j<i ==> b[j] == a[(j+offset) % n]
  {
    b[i] := a[(i+offset) % n];
  }
}
// </vc-code>

