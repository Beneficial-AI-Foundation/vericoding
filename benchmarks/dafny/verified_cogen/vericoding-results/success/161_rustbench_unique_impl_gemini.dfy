// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Unique(a: array<int>) returns (result: array<int>)
    requires forall i, j :: 0 <= i && i < j && j < a.Length ==> a[i] <= a[j]
    ensures forall i, j :: 0 <= i && i < j && j < result.Length ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix illegal array slice assignment and forall quantifier syntax */
    var s: seq<int> := [];
    if a.Length > 0 {
        s := [a[0]];
        var i := 1;
        while i < a.Length
            invariant 1 <= i <= a.Length
            invariant |s| >= 1
            invariant forall j, k :: 0 <= j < k < |s| ==> s[j] < s[k]
            invariant forall x :: x in s ==> x in multiset(a[..i])
        {
            if a[i] > s[|s|-1] {
                s := s + [a[i]];
            }
            i := i + 1;
        }
    }
    result := new int[|s|];
    forall k | 0 <= k < |s| {
        result[k] := s[k];
    }
}
// </vc-code>
