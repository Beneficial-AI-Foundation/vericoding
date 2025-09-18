// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simple ReplaceAt without ensures */
function ReplaceAt(s: seq<int>, j: int, v: int): seq<int>
  requires 0 <= j < |s|
{
  s[..j] + [v] + s[j+1..]
}
// </vc-helpers>

// <vc-spec>
method TestArrayElements(a: seq<int>, j: nat) returns (result: seq<int>)
    requires j < |a|
    ensures |result| == |a|
    ensures result[j] == 60
    ensures forall k :: 0 <= k < |a| && k != j ==> result[k] == a[k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): set a[j] to 60 using slicing */
  result := a[..j] + [60] + a[j+1..];
}
// </vc-code>
