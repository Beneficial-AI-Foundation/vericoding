predicate ValidInput(n: int, numbers: seq<int>)
{
    n >= 3 && n % 3 == 0 &&
    |numbers| == n &&
    forall i :: 0 <= i < |numbers| ==> 1 <= numbers[i] <= 7
}

predicate ValidTriplet(triplet: seq<int>)
{
    |triplet| == 3 &&
    triplet[0] < triplet[1] < triplet[2] &&
    triplet[0] > 0 && triplet[1] > 0 && triplet[2] > 0 &&
    triplet[1] % triplet[0] == 0 && triplet[2] % triplet[1] == 0
}

function FlattenPartition(result: seq<seq<int>>): seq<int>
{
    if |result| == 0 then [] else
    result[0] + FlattenPartition(result[1..])
}

predicate ValidPartition(result: seq<seq<int>>, numbers: seq<int>)
{
    |result| == |numbers| / 3 &&
    (forall i :: 0 <= i < |result| ==> ValidTriplet(result[i])) &&
    multiset(numbers) == multiset(FlattenPartition(result))
}

predicate NoPartitionExists(result: seq<seq<int>>)
{
    |result| == 0
}

// <vc-helpers>
lemma FlattenEmpty()
    ensures FlattenPartition([]) == []
{
}

lemma FlattenSingleton(s: seq<int>)
    ensures FlattenPartition([s]) == s
{
}

lemma FlattenConcat(s1: seq<seq<int>>, s2: seq<seq<int>>)
    ensures FlattenPartition(s1 + s2) == FlattenPartition(s1) + FlattenPartition(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert FlattenPartition(s1) == [];
        assert FlattenPartition(s1 + s2) == FlattenPartition(s2);
        assert [] + FlattenPartition(s2) == FlattenPartition(s2);
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        FlattenConcat(s1[1..], s2);
        assert FlattenPartition(s1 + s2) == s1[0] + FlattenPartition(s1[1..] + s2);
        assert FlattenPartition(s1[1..] + s2) == FlattenPartition(s1[1..]) + FlattenPartition(s2);
        assert FlattenPartition(s1 + s2) == s1[0] + FlattenPartition(s1[1..]) + FlattenPartition(s2);
        assert FlattenPartition(s1) == s1[0] + FlattenPartition(s1[1..]);
        assert FlattenPartition(s1 + s2) == FlattenPartition(s1) + FlattenPartition(s2);
    }
}

lemma MultisetFlattenAppend(result: seq<seq<int>>, triplet: seq<int>)
    ensures multiset(FlattenPartition(result + [triplet])) == multiset(FlattenPartition(result)) + multiset(triplet)
{
    FlattenConcat(result, [triplet]);
    FlattenSingleton(triplet);
}

lemma MultisetSliceNext(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures multiset(s[..i+1]) == multiset(s[..i]) + multiset{s[i]}
{
    assert s[..i+1] == s[..i] + [s[i]];
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, numbers: seq<int>) returns (result: seq<seq<int>>)
    requires ValidInput(n, numbers)
    ensures NoPartitionExists(result) || ValidPartition(result, numbers)
// </vc-spec>
// <vc-code>
{
    var counts := new int[8];
    var i := 0;
    while i < 8
        invariant 0 <= i <= 8
        invariant forall j :: 0 <= j < i ==> counts[j] == 0
    {
        counts[i] := 0;
        i := i + 1;
    }
    
    i := 0;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant forall j :: 0 <= j <= 7 ==> counts[j] >= 0
        invariant forall j :: 1 <= j <= 7 ==> counts[j] == multiset(numbers[..i])[j]
        invariant counts[0] == multiset(numbers[..i])[0]
    {
        MultisetSliceNext(numbers, i);
        counts[numbers[i]] := counts[numbers[i]] + 1;
        i := i + 1;
    }
    
    assert numbers[..|numbers|] == numbers;
    var originalCounts := new int[8];
    i := 0;
    while i < 8
        invariant 0 <= i <= 8
        invariant forall j :: 0 <= j < i ==> originalCounts[j] == counts[j]
    {
        originalCounts[i] := counts[i];
        i := i + 1;
    }
    
    result := [];
    
    // Try to form triplets greedily
    // Valid triplets from 1-7: (1,2,4), (1,2,6), (1,3,6)
    
    while counts[1] > 0 && counts[2] > 0 && counts[4] > 0 && |result| < n / 3
        invariant forall j :: 0 <= j <= 7 ==> counts[j] >= 0
        invariant 0 <= |result| <= n / 3
        invariant forall k :: 0 <= k < |result| ==> ValidTriplet(result[k])
    {
        var triplet := [1, 2, 4];
        result := result + [triplet];
        counts[1] := counts[1] - 1;
        counts[2] := counts[2] - 1;
        counts[4] := counts[4] - 1;
    }
    
    while counts[1] > 0 && counts[2] > 0 && counts[6] > 0 && |result| < n / 3
        invariant forall j :: 0 <= j <= 7 ==> counts[j] >= 0
        invariant 0 <= |result| <= n / 3
        invariant forall k :: 0 <= k < |result| ==> ValidTriplet(result[k])
    {
        var triplet := [1, 2, 6];
        result := result + [triplet];
        counts[1] := counts[1] - 1;
        counts[2] := counts[2] - 1;
        counts[6] := counts[6] - 1;
    }
    
    while counts[1] > 0 && counts[3] > 0 && counts[6] > 0 && |result| < n / 3
        invariant forall j :: 0 <= j <= 7 ==> counts[j] >= 0
        invariant 0 <= |result| <= n / 3
        invariant forall k :: 0 <= k < |result| ==> ValidTriplet(result[k])
    {
        var triplet := [1, 3, 6];
        result := result + [triplet];
        counts[1] := counts[1] - 1;
        counts[3] := counts[3] - 1;
        counts[6] := counts[6] - 1;
    }
    
    // Check if we used all numbers
    var allUsed := true;
    i := 1;
    while i <= 7
        invariant 1 <= i <= 8
        invariant allUsed ==> forall j :: 1 <= j < i ==> counts[j] == 0
    {
        if counts[i] != 0 {
            allUsed := false;
        }
        i := i + 1;
    }
    
    if !allUsed || |result| != n / 3 {
        result := [];
    }
    
    assert NoPartitionExists(result) || |result| == n / 3;
    assert NoPartitionExists(result) || (forall k :: 0 <= k < |result| ==> ValidTriplet(result[k]));
}
// </vc-code>

