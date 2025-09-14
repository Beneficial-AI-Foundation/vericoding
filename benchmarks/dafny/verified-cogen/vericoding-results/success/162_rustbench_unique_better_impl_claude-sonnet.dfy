// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed assertion by proving that RemoveDuplicates maintains order property */
predicate IsStrictlyIncreasing(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

function RemoveDuplicates(s: seq<int>): seq<int>
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures IsStrictlyIncreasing(RemoveDuplicates(s))
    ensures forall x :: x in RemoveDuplicates(s) ==> x in s
    decreases |s|
{
    if |s| <= 1 then s
    else if s[0] == s[1] then RemoveDuplicates(s[1..])
    else 
        var rest := RemoveDuplicates(s[1..]);
        assert s[0] < s[1];
        assert forall i, j :: 0 <= i < j < |s[1..]| ==> s[1..][i] <= s[1..][j];
        assert forall i :: 0 <= i < |rest| ==> rest[i] in s[1..];
        assert forall i :: 0 <= i < |rest| ==> rest[i] >= s[1];
        assert forall i :: 0 <= i < |rest| ==> s[0] < rest[i];
        [s[0]] + rest
}

lemma SlicePreservesNonDecreasing(s: seq<int>, start: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires 0 <= start < |s|
    ensures forall i, j :: 0 <= i < j < |s[start..]| ==> s[start..][i] <= s[start..][j]
{
}

lemma RemoveDuplicatesPreservesOrder(s: seq<int>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures forall x :: x in RemoveDuplicates(s) ==> x in s
    ensures forall i :: 0 <= i < |RemoveDuplicates(s)| ==> RemoveDuplicates(s)[i] in s
    decreases |s|
{
    if |s| <= 1 {
    } else if s[0] == s[1] {
        SlicePreservesNonDecreasing(s, 1);
        RemoveDuplicatesPreservesOrder(s[1..]);
    } else {
        SlicePreservesNonDecreasing(s, 1);
        RemoveDuplicatesPreservesOrder(s[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method UniqueBetter(a: array<int>) returns (result: seq<int>)
    requires
        forall i: int, j: int ::
            0 <= i && i < j && j < a.Length ==> a[i] <= a[j]
    ensures
        forall i: int, j: int ::
            0 <= i && i < j && j < |result| ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): call helper lemmas to establish postcondition */
{
    var seq_a := a[..];
    RemoveDuplicatesPreservesOrder(seq_a);
    result := RemoveDuplicates(seq_a);
}
// </vc-code>
