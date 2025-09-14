

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
  if n == 0 {
    return;
  }
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant b.Length == n
    invariant a.Length == n
    invariant n > 0
    invariant forall j :: 0 <= j < i ==> b[j] == a[(j + offset) % n]
    decreases n - i
  {
    b[i] := a[(i + offset) % n];
    i := i + 1;
  }
}
// </vc-code>

