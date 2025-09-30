

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart..len+dStart] == src[sStart..len+sStart]
// </vc-spec>
// <vc-code>
{
  r := new int[dest.Length];
  var i := 0;
  while i < dest.Length
    invariant 0 <= i <= dest.Length
    invariant r.Length == dest.Length
    invariant forall j :: 0 <= j < i && j < dStart ==> r[j] == dest[j]
    invariant forall j :: 0 <= j < i && dStart <= j < dStart + len ==> r[j] == src[sStart + (j - dStart)]
    invariant forall j :: 0 <= j < i && j >= dStart + len ==> r[j] == dest[j]
  {
    if i < dStart {
      r[i] := dest[i];
    } else if i < dStart + len {
      r[i] := src[sStart + (i - dStart)];
    } else {
      r[i] := dest[i];
    }
    i := i + 1;
  }
}
// </vc-code>

