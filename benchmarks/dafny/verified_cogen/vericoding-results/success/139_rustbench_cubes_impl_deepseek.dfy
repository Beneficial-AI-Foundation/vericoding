// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Cubes(len: int) returns (result: array<int>)
    requires len >= 0
    ensures result.Length == len
    ensures forall i :: 0 <= i < len ==> result[i] == i * i * i
// </vc-spec>
// <vc-code>
{
  result := new int[len];
  var pos := 0;
  while pos < len
    invariant pos <= len
    invariant result.Length == len
    invariant forall i :: 0 <= i < pos ==> result[i] == i*i*i
  {
    result[pos] := pos * pos * pos;
    pos := pos + 1;
  }
}
// </vc-code>
