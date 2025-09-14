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
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant forall j :: 0 <= j < i ==> result[j] == j * j * j
  {
    result[i] := i * i * i;
    i := i + 1;
  }
}
// </vc-code>
