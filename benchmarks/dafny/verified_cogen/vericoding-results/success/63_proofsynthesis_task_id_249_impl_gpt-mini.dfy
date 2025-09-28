// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause to allow array element access in functions */
function ArrContains(a: array<int>, x: int): bool reads a { exists i :: 0 <= i < a.Length && a[i] == x }
/* helper modified by LLM (iteration 2): sequence membership helper */
function SeqContains(s: seq<int>, x: int): bool { exists i :: 0 <= i < |s| && s[i] == x }
// </vc-helpers>

// <vc-spec>
method intersection(arr1: array<int>, arr2: array<int>) returns (result: array<int>)
    ensures
        forall i :: 0 <= i < result.Length ==> (result[i] in arr1[..] && result[i] in arr2[..])
    ensures
        forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build unique intersection into sequence then copy to result array */
  var s: seq<int> := [];
  var i := 0;
  while i < arr1.Length
    invariant 0 <= i <= arr1.Length
    invariant forall j :: 0 <= j < |s| ==> ArrContains(arr1, s[j]) && ArrContains(arr2, s[j])
    invariant forall p, q :: 0 <= p < q < |s| ==> s[p] != s[q]
  {
    var x := arr1[i];
    if ArrContains(arr2, x) && !SeqContains(s, x) {
      s := s + [x];
    }
    i := i + 1;
  }
  result := new int[|s|];
  var k := 0;
  while k < |s|
    invariant 0 <= k <= |s|
    invariant forall j :: 0 <= j < k ==> result[j] == s[j]
    invariant forall p, q :: 0 <= p < q < k ==> result[p] != result[q]
  {
    result[k] := s[k];
    k := k + 1;
  }
}

// </vc-code>
