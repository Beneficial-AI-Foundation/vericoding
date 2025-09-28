// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */
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
/* code modified by LLM (iteration 3): added invariant for first part in second loop to aid verification */
var len1 := first.Length - 1;
var len2 := second.Length;
var result := new int[len1 + len2];
var i := 0;
while i < len1
  invariant 0 <= i <= len1
  invariant forall j :: 0 <= j < i ==> result[j] == first[j]
{
  result[i] := first[i];
  i := i + 1;
}
i := 0;
while i < len2
  invariant 0 <= i <= len2
  invariant forall j :: 0 <= j < len1 ==> result[j] == first[j]
  invariant forall j :: 0 <= j < i ==> result[len1 + j] == second[j]
{
  result[len1 + i] := second[i];
  i := i + 1;
}
replacedList := result;
}
// </vc-code>
