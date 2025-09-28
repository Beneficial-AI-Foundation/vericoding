// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
  var n1 := first.Length;
  var n2 := second.Length;
  var total := n1 - 1 + n2;
  replacedList := new int[total];
  var i := 0;
  while i < n1 - 1
    invariant 0 <= i <= n1 - 1
    invariant replacedList.Length == total
    invariant forall j :: 0 <= j < i ==> replacedList[j] == first[j]
  {
    replacedList[i] := first[i];
    i := i + 1;
  }
  var k := 0;
  while k < n2
    invariant 0 <= k <= n2
    invariant i == n1 - 1
    invariant replacedList.Length == total
    invariant forall j :: 0 <= j < i ==> replacedList[j] == first[j]
    invariant forall j :: 0 <= j < k ==> replacedList[n1 - 1 + j] == second[j]
  {
    replacedList[n1 - 1 + k] := second[k];
    k := k + 1;
  }
}
// </vc-code>
