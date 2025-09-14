// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide cube function used for clarity */
function cube(n: int): int { n * n * n }
// </vc-helpers>

// <vc-spec>
method Cubes(len: int) returns (result: array<int>)
    requires len >= 0
    ensures result.Length == len
    ensures forall i :: 0 <= i < len ==> result[i] == i * i * i
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented loop to compute cubes and removed redundant null invariant */
  result := new int[len];
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant result.Length == len
    invariant forall j :: 0 <= j < i ==> result[j] == j * j * j
    decreases len - i
  {
    result[i] := i * i * i;
    i := i + 1;
  }
}
// </vc-code>
