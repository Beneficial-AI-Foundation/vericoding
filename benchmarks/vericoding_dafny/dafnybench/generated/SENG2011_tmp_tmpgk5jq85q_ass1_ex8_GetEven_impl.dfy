// successfully verifies

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method GetEven(a: array<nat>)
requires true;
ensures forall i:int :: 0<=i<a.Length ==> a[i] % 2 == 0
modifies a
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j:int :: 0 <= j < i ==> a[j] % 2 == 0
  {
    if a[i] % 2 == 1 {
      a[i] := a[i] + 1;
    }
    i := i + 1;
  }
}
// </vc-code>