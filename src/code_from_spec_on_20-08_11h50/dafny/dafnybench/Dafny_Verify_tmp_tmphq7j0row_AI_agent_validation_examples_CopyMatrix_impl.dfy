// <vc-spec>
method CopyMatrix(source: array2<int>, dest: array2<int>)
  requires source.Length0 == dest.Length0
  requires source.Length1 == dest.Length1
  modifies dest
  ensures forall i, j :: 0 <= i < dest.Length0 && 0 <= j < dest.Length1 ==> dest[i, j] == source[i, j]
// </vc-spec>

// <vc-code>
{
  var i := 0;
  while i < source.Length0
    invariant 0 <= i <= source.Length0
    invariant forall r, c :: 0 <= r < i && 0 <= c < dest.Length1 ==> dest[r, c] == source[r, c]
  {
    var j := 0;
    while j < source.Length1
      invariant 0 <= j <= source.Length1
      invariant forall r, c :: 0 <= r < i && 0 <= c < dest.Length1 ==> dest[r, c] == source[r, c]
      invariant forall c :: 0 <= c < j ==> dest[i, c] == source[i, c]
    {
      dest[i, j] := source[i, j];
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

// <vc-helpers>
// No helper functions needed for this implementation
// </vc-helpers>