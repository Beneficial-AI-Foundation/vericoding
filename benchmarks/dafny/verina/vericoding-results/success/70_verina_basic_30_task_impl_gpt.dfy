// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple wrapper for modulo operation to aid reasoning */
function Mod(a: int, b: int): int
  requires b != 0
{ a % b }
// </vc-helpers>

// <vc-spec>
method ElementWiseModulo(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires |a| > 0
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] % b[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build result iteratively to avoid comprehension parse issues and ensure correctness */
  var r: seq<int> := [];
  var i: int := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == a[j] % b[j]
  {
    r := r + [a[i] % b[i]];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
