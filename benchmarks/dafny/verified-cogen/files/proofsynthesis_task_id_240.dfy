// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
    assume {:axiom} false;
}
// </vc-code>
