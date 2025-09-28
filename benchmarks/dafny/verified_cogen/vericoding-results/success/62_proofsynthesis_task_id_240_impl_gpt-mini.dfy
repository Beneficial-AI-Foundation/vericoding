// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide min function */
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method ReplaceLastElement(first: array<int>, second: array<int>) returns (replacedList: array<int>)
    requires first.Length > 0
    ensures replacedList.Length == first.Length - 1 + second.Length
    ensures forall i :: 0 <= i < first.Length - 1 ==> replacedList[i] == first[i]
    ensures forall i :: 0 <= i < second.Length ==> replacedList[first.Length - 1 + i] == second[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): copy first elements then append second; preserve invariants for verification */
  replacedList := new int[first.Length - 1 + second.Length];
  var i := 0;
  while i < first.Length - 1
    invariant 0 <= i <= first.Length - 1
    invariant forall k :: 0 <= k < i ==> replacedList[k] == first[k]
  {
    replacedList[i] := first[i];
    i := i + 1;
  }
  var j := 0;
  while j < second.Length
    invariant 0 <= j <= second.Length
    invariant forall k :: 0 <= k < j ==> replacedList[first.Length - 1 + k] == second[k]
    invariant forall k :: 0 <= k < first.Length - 1 ==> replacedList[k] == first[k]
  {
    replacedList[first.Length - 1 + j] := second[j];
    j := j + 1;
  }
}
// </vc-code>
