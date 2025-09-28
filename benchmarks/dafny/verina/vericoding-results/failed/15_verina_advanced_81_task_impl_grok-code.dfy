// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
predicate IsSorted(s: seq<int>) {
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}
predicate HasUnique(s: seq<int>) {
  forall i,j :: 0 <= i < j < |s| ==> s[i] != s[j]
}
/* helper modified by LLM (iteration 5): Added IsSorted and HasUnique predicates to verify sortedness and uniqueness in loop invariants */

// </vc-helpers>

// <vc-spec>
method UniqueSorted(arr: array<int>) returns (result: array<int>)
    ensures result.Length <= arr.Length
    ensures forall i :: 0 <= i < result.Length - 1 ==> result[i] <= result[i + 1]
    ensures forall x :: x in arr[..] <==> x in result[..]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Added predicates for IsSorted and HasUnique in invariants, and strengthened loop invariants to maintain sortedness, uniqueness, and set membership */
  var resultSeq: seq<int> := [];
  var k := 0;
  while k < arr.Length
    invariant 0 <= k <= arr.Length
    invariant |resultSeq| <= k
    invariant IsSorted(resultSeq)
    invariant HasUnique(resultSeq)
    invariant forall x :: x in resultSeq <==> x in arr[0..k]
  {
    var elem := arr[k];
    var j := 0;
    while j < |resultSeq| && resultSeq[j] < elem
      invariant 0 <= j <= |resultSeq|
      invariant forall i :: 0 <= i < j ==> resultSeq[i] < elem
      invariant IsSorted(resultSeq)
      invariant HasUnique(resultSeq)
    {
      j := j + 1;
    }
    if j >= |resultSeq| || resultSeq[j] != elem {
      resultSeq := resultSeq[..j] + [elem] + resultSeq[j..];
    }
    k := k + 1;
  }
  result := new int[|resultSeq|];
  if |resultSeq| > 0 {
    for idx := 0 to |resultSeq| - 1
    {
      result[idx] := resultSeq[idx];
    }
  }
}
// </vc-code>
