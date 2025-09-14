// <vc-preamble>
// </vc-preamble>

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
  var i: nat := 0;
  while i < r.Length
    invariant 0 <= i <= r.Length
    invariant forall k :: 0 <= k < i ==> 
      if dStart <= k < dStart + len then 
        r[k] == src[sStart + k - dStart] 
      else 
        r[k] == dest[k]
  {
    if dStart <= i < dStart + len {
      r[i] := src[sStart + i - dStart];
    } else {
      r[i] := dest[i];
    }
    i := i + 1;
  }
}
// </vc-code>
