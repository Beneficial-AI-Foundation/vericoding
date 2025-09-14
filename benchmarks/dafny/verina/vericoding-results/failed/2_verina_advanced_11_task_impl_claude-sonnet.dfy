// <vc-preamble>
function CountOccurrences(x: int, lst: seq<int>): nat
{
    |set i | 0 <= i < |lst| && lst[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed set cardinality proof and disjointness reasoning */
predicate IsMajority(x: int, lst: seq<int>)
{
    CountOccurrences(x, lst) > |lst| / 2
}

function CountOccurrencesInArray(x: int, arr: array<int>, end: nat): nat
    requires end <= arr.Length
    reads arr
{
    CountOccurrences(x, arr[..end])
}

lemma CountOccurrencesProperty(x: int, arr: array<int>, i: nat)
    requires i < arr.Length
    ensures CountOccurrencesInArray(x, arr, i+1) == CountOccurrencesInArray(x, arr, i) + (if arr[i] == x then 1 else 0)
{
    var s1 := arr[..i];
    var s2 := arr[..i+1];
    assert s2 == s1 + [arr[i]];
    
    assert CountOccurrences(x, s2) == |set j | 0 <= j < |s2| && s2[j] == x|;
    assert CountOccurrences(x, s1) == |set j | 0 <= j < |s1| && s1[j] == x|;
    
    var set1 := set j | 0 <= j < |s1| && s1[j] == x;
    var set2 := set j | 0 <= j < |s2| && s2[j] == x;
    
    if arr[i] == x {
        assert set2 == set1 + {|s1|};
        assert |s1| !in set1;
        assert |set2| == |set1| + 1;
    } else {
        assert set2 == set1;
        assert |set2| == |set1|;
    }
}

lemma MajorityUniqueness(lst: seq<int>)
    ensures forall x, y :: x != y && CountOccurrences(x, lst) > |lst| / 2 && CountOccurrences(y, lst) > |lst| / 2 ==> false
{
    forall x, y | x != y && CountOccurrences(x, lst) > |lst| / 2 && CountOccurrences(y, lst) > |lst| / 2
        ensures false
    {
        var setX := set i | 0 <= i < |lst| && lst[i] == x;
        var setY := set i | 0 <= i < |lst| && lst[i] == y;
        var universeSet := set i | 0 <= i < |lst|;
        assert setX !! setY;
        assert setX <= universeSet;
        assert setY <= universeSet;
        assert setX + setY <= universeSet;
        assert |setX + setY| == |setX| + |setY|;
        assert |setX + setY| <= |universeSet|;
        assert |setX| + |setY| <= |lst|;
        assert CountOccurrences(x, lst) + CountOccurrences(y, lst) <= |lst|;
        assert CountOccurrences(x, lst) > |lst| / 2;
        assert CountOccurrences(y, lst) > |lst| / 2;
        assert CountOccurrences(x, lst) + CountOccurrences(y, lst) > |lst|;
    }
}

lemma MajorityExistsImpliesUnique(x: int, lst: seq<int>)
    requires CountOccurrences(x, lst) > |lst| / 2
    ensures forall y :: y != x ==> CountOccurrences(y, lst) <= |lst| / 2
{
    forall y | y != x
        ensures CountOccurrences(y, lst) <= |lst| / 2
    {
        if CountOccurrences(y, lst) > |lst| / 2 {
            MajorityUniqueness(lst);
            assert false;
        }
    }
}

lemma NoMajorityLemma(candidate: int, lst: seq<int>)
    requires CountOccurrences(candidate, lst) <= |lst| / 2
    ensures forall x :: CountOccurrences(x, lst) <= |lst| / 2
{
    forall x
        ensures CountOccurrences(x, lst) <= |lst| / 2
    {
        if CountOccurrences(x, lst) > |lst| / 2 {
            MajorityUniqueness(lst);
            assert false;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method FindMajorityElement(lst: array<int>) returns (result: int)
    ensures var lst_seq := lst[..];
            var n := |lst_seq|;
            var majority := CountOccurrences(result, lst_seq) > n / 2 && 
                          forall x :: CountOccurrences(x, lst_seq) <= n / 2 || x == result;
            (result == -1 ==> forall x :: CountOccurrences(x, lst_seq) <= n / 2) &&
            (result != -1 ==> majority)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed postcondition proof with proper helper lemma */
    if lst.Length == 0 {
        result := -1;
        return;
    }
    
    var candidate := lst[0];
    var count := 0;
    var i := 0;
    
    while i < lst.Length
        invariant 0 <= i <= lst.Length
    {
        if count == 0 {
            candidate := lst[i];
            count := 1;
        } else if lst[i] == candidate {
            count := count + 1;
        } else {
            count := count - 1;
        }
        i := i + 1;
    }
    
    var actualCount := 0;
    i := 0;
    while i < lst.Length
        invariant 0 <= i <= lst.Length
        invariant actualCount == CountOccurrencesInArray(candidate, lst, i)
    {
        CountOccurrencesProperty(candidate, lst, i);
        if lst[i] == candidate {
            actualCount := actualCount + 1;
        }
        i := i + 1;
    }
    
    if actualCount > lst.Length / 2 {
        result := candidate;
        assert CountOccurrences(result, lst[..]) > |lst[..]| / 2;
        MajorityExistsImpliesUnique(result, lst[..]);
        assert forall x :: CountOccurrences(x, lst[..]) <= |lst[..]| / 2 || x == result;
    } else {
        result := -1;
        assert CountOccurrences(candidate, lst[..]) <= lst.Length / 2;
        NoMajorityLemma(candidate, lst[..]);
        assert forall x :: CountOccurrences(x, lst[..]) <= |lst[..]| / 2;
    }
}
// </vc-code>
