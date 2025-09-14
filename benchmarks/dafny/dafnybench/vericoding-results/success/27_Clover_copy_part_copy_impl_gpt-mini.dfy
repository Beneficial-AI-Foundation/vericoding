

// <vc-helpers>
// helper proofs (none needed)
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
  var k := 0;
  while k < dStart
    invariant 0 <= k <= dStart
    invariant r[..k] == dest[..k]
  {
    r[k] := dest[k];
    k := k + 1;
  }

  var j := 0;
  while j < len
    invariant 0 <= j <= len
    invariant r[..dStart] == dest[..dStart]
    invariant r[dStart .. dStart + j] == src[sStart .. sStart + j]
  {
    r[dStart + j] := src[sStart + j];
    j := j + 1;
  }

  var p := dStart + len;
  while p < dest.Length
    invariant dStart + len <= p <= dest.Length
    invariant r[..dStart] == dest[..dStart]
    invariant r[dStart .. dStart + len] == src[sStart .. sStart + len]
    invariant r[dStart + len .. p] == dest[dStart + len .. p]
  {
    r[p] := dest[p];
    p := p + 1;
  }

  return r;
}
// </vc-code>

