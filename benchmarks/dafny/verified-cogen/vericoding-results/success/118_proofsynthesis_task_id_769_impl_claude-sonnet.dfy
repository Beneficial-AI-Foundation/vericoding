// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function InSeq(x: int, s: seq<int>): bool {
    exists i :: 0 <= i < |s| && s[i] == x
}

function RemoveDuplicates(s: seq<int>): seq<int>
    decreases |s|
{
    if |s| == 0 then []
    else if InSeq(s[0], s[1..]) then RemoveDuplicates(s[1..])
    else [s[0]] + RemoveDuplicates(s[1..])
}

lemma InSeqCorrect(x: int, s: seq<int>)
    ensures InSeq(x, s) <==> x in s
{
    if |s| == 0 {
        assert !InSeq(x, s) && x !in s;
    } else {
        if s[0] == x {
            assert InSeq(x, s) && x in s;
        } else {
            InSeqCorrect(x, s[1..]);
            assert InSeq(x, s) <==> InSeq(x, s[1..]);
            assert x in s <==> x in s[1..];
        }
    }
}

lemma RemoveDuplicatesPreservesElements(s: seq<int>)
    ensures forall x :: x in s ==> x in RemoveDuplicates(s)
    decreases |s|
{
    if |s| == 0 {
        assert forall x :: x in s ==> x in RemoveDuplicates(s);
    } else {
        RemoveDuplicatesPreservesElements(s[1..]);
        if InSeq(s[0], s[1..]) {
            assert s[0] in s[1..];
            assert RemoveDuplicates(s) == RemoveDuplicates(s[1..]);
            assert s[0] in RemoveDuplicates(s[1..]);
        } else {
            assert RemoveDuplicates(s) == [s[0]] + RemoveDuplicates(s[1..]);
            assert s[0] in RemoveDuplicates(s);
        }
    }
}

lemma RemoveDuplicatesElementsNotInTail(s: seq<int>)
    requires |s| > 0
    requires !InSeq(s[0], s[1..])
    ensures forall i :: 0 <= i < |RemoveDuplicates(s[1..])| ==> RemoveDuplicates(s[1..])[i] != s[0]
    decreases |s|
{
    InSeqCorrect(s[0], s[1..]);
    assert s[0] !in s[1..];
    RemoveDuplicatesPreservesElementsOnly(s[1..]);
}

lemma RemoveDuplicatesPreservesElementsOnly(s: seq<int>)
    ensures forall x :: x in RemoveDuplicates(s) ==> x in s
    decreases |s|
{
    if |s| == 0 {
        assert |RemoveDuplicates(s)| == 0;
    } else {
        RemoveDuplicatesPreservesElementsOnly(s[1..]);
        if InSeq(s[0], s[1..]) {
            assert RemoveDuplicates(s) == RemoveDuplicates(s[1..]);
        } else {
            assert RemoveDuplicates(s) == [s[0]] + RemoveDuplicates(s[1..]);
        }
    }
}

lemma RemoveDuplicatesNoDuplicates(s: seq<int>)
    ensures forall i, j :: 0 <= i < j < |RemoveDuplicates(s)| ==> RemoveDuplicates(s)[i] != RemoveDuplicates(s)[j]
    decreases |s|
{
    if |s| == 0 {
        assert |RemoveDuplicates(s)| == 0;
    } else {
        RemoveDuplicatesNoDuplicates(s[1..]);
        if InSeq(s[0], s[1..]) {
            assert RemoveDuplicates(s) == RemoveDuplicates(s[1..]);
        } else {
            var rd := RemoveDuplicates(s[1..]);
            assert RemoveDuplicates(s) == [s[0]] + rd;
            RemoveDuplicatesElementsNotInTail(s);
            assert forall i :: 0 <= i < |rd| ==> rd[i] != s[0];
        }
    }
}

/* helper modified by LLM (iteration 3): added RemoveDuplicatesElementsNotInTail lemma to prove no duplicates property */
// </vc-helpers>

// <vc-spec>
method difference(arr1: seq<int>, arr2: seq<int>) returns (result: seq<int>)
    ensures
        (forall i :: 0 <= i < |arr1| ==> (arr1[i] !in arr2 ==> arr1[i] in result)) &&
        (forall i :: 0 <= i < |arr2| ==> (arr2[i] !in arr1 ==> arr2[i] in result)) &&
        (forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added proper loop invariants and lemma calls */
    var temp: seq<int> := [];
    
    for i := 0 to |arr1|
        invariant 0 <= i <= |arr1|
        invariant forall k :: 0 <= k < i ==> (arr1[k] !in arr2 ==> arr1[k] in temp)
    {
        InSeqCorrect(arr1[i], arr2);
        if !InSeq(arr1[i], arr2) {
            temp := temp + [arr1[i]];
        }
    }
    
    for i := 0 to |arr2|
        invariant 0 <= i <= |arr2|
        invariant forall k :: 0 <= k < |arr1| ==> (arr1[k] !in arr2 ==> arr1[k] in temp)
        invariant forall k :: 0 <= k < i ==> (arr2[k] !in arr1 ==> arr2[k] in temp)
    {
        InSeqCorrect(arr2[i], arr1);
        if !InSeq(arr2[i], arr1) {
            temp := temp + [arr2[i]];
        }
    }
    
    RemoveDuplicatesPreservesElements(temp);
    RemoveDuplicatesNoDuplicates(temp);
    result := RemoveDuplicates(temp);
}
// </vc-code>
