// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed helper functions for cyclic decoding */
function IsInUnchangedPart(len: int, i: int): bool {
  len - len % 3 <= i < len
}

function GetSourceIndex(len: int, i: int): int {
  if IsInUnchangedPart(len, i) then i
  else if i % 3 == 0 then i + 2
  else i - 1
}
// </vc-helpers>

// <vc-spec>
method decode_cyclic(s: seq<int>) returns (res: seq<int>)

    ensures |s| == |res|
    ensures forall i :: |s| - |s| % 3 <= i < |s| ==> (res[i] == s[i])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 0 ==> res[i] == s[i + 2])
    ensures forall i :: 0 <= i < |s| - |s| % 3 ==> (i % 3 == 1 ==> res[i] == s[i - 1])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added invariant to relate res elements to source indices */
{
  var len := |s|;
  res := [];
  for i := 0 to len
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == s[GetSourceIndex(len, j)]
  {
    if i < len {
      res := res + [s[GetSourceIndex(len, i)]];
    }
  }
}
// </vc-code>
