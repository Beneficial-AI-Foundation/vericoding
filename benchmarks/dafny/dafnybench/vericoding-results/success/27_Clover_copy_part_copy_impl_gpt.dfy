

// <vc-helpers>
// no helpers needed
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
  while i < dStart
    invariant 0 <= i <= dStart
    invariant r.Length == dest.Length
    invariant dStart <= dest.Length
    invariant r[..i] == dest[..i]
    decreases dStart - i
  {
    assert i < dest.Length;
    assert i < r.Length;
    r[i] := dest[i];
    i := i + 1;
  }

  var j := 0;
  while j < len
    invariant 0 <= j <= len
    invariant r.Length == dest.Length
    invariant dStart <= dest.Length
    invariant sStart <= src.Length
    invariant dStart + j <= dest.Length
    invariant sStart + j <= src.Length
    invariant r[..dStart] == dest[..dStart]
    invariant r[dStart..dStart + j] == src[sStart..sStart + j]
    decreases len - j
  {
    assert dStart + j < dest.Length;
    assert dStart + j < r.Length;
    assert sStart + j < src.Length;
    r[dStart + j] := src[sStart + j];
    j := j + 1;
  }

  var k := dStart + len;
  while k < dest.Length
    invariant r.Length == dest.Length
    invariant dStart + len <= k <= dest.Length
    invariant r[..dStart] == dest[..dStart]
    invariant r[dStart..dStart + len] == src[sStart..sStart + len]
    invariant r[dStart + len .. k] == dest[dStart + len .. k]
    decreases dest.Length - k
  {
    assert k < dest.Length;
    assert k < r.Length;
    r[k] := dest[k];
    k := k + 1;
  }

  assert k == dest.Length;
  assert r.Length == dest.Length;
  assert k == r.Length;
  assert r[dStart + len ..] == r[dStart + len .. k];
  assert dest[dStart + len ..] == dest[dStart + len .. k];
  assert r[dStart + len .. k] == dest[dStart + len .. k];
  assert r[dStart + len ..] == dest[dStart + len ..];
}
// </vc-code>

