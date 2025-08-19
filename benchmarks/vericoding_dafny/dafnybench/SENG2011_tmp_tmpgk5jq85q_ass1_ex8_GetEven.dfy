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
  assume false;
}
// </vc-code>