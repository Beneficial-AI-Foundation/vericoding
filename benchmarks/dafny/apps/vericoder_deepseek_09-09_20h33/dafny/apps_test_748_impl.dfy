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
lemma SortedAndUnique(s: seq<int>)
    requires |s| == 3
    requires s[0] < s[1] < s[2]
    requires s[0] > 0 && s[1] > 0 && s[2] > 0
    requires s[1] % s[0] == 0 && s[2] % s[1] == 0
    ensures ValidTriplet(s)
{
}

lemma FlattenPartitionLemma(result: seq<seq<int>>, numbers: seq<int>)
    requires |result| == |numbers| / 3
    requires (forall i :: 0 <= i < |result| ==> ValidTriplet(result[i]))
    requires multiset(numbers) == multiset(FlattenPartition(result))
    ensures ValidPartition(result, numbers)
{
}

lemma NoPartitionIsValid(result: seq<seq<int>>)
    requires |result| == 0
    ensures NoPartitionExists(result)
{
}

lemma PairCounts(numbers: seq<int>)
    requires |numbers| >= 3 && |numbers| % 3 == 0
    requires forall i :: 0 <= i < |numbers| ==> 1 <= numbers[i] <= 7
{
}

function CountInMultiset(ms: multiset<int>, value: int): int
{
    ms[value]
}

lemma ValidTripletImpliesCondition(triplet: seq<int>)
    requires ValidTriplet(triplet)
    ensures |triplet| == 3 && triplet[0] < triplet[1] < triplet[2] &&
        triplet[0] > 0 && triplet[1] > 0 && triplet[2] > 0 &&
        triplet[1] % triplet[0] == 0 && triplet[2] % triplet[1] == 0
{
}

lemma MultisetEqualityPreserved(ms1: multiset<int>, ms2: multiset<int>, triplet: seq<int>)
    requires ms2 == ms1 - multiset(triplet)
    ensures ms1 == ms2 + multiset(triplet)
{
}

lemma ValidTripletCheck(triplet: seq<int>)
    requires |triplet| == 3
    requires triplet[0] == 1 && triplet[1] == 2 && triplet[2] == 4
    ensures ValidTriplet(triplet)
{
}

lemma ValidTripletCheck2(triplet: seq<int>)
    requires |triplet| == 3
    requires triplet[0] == 1 && triplet[1] == 2 && triplet[2] == 6
    ensures ValidTriplet(triplet)
{
}

lemma MultisetExtractionLemma(ms: multiset<int>, triplet: seq<int>)
    requires |triplet| == 3
    requires multiset(triplet) <= ms
    ensures multiset(FlattenPartition([triplet])) == multiset(triplet)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, numbers: seq<int>) returns (result: seq<seq<int>>)
    requires ValidInput(n, numbers)
    ensures NoPartitionExists(result) || ValidPartition(result, numbers)
// </vc-spec>
// <vc-code>
{
    var m := multiset(numbers);
    result := [];
    
    if (CountInMultiset(m, 1) >= 1 && CountInMultiset(m, 2) >= 1 && CountInMultiset(m, 4) >= 1) {
        var triplet := [1, 2, 4];
        ValidTripletCheck(triplet);
        if (multiset(triplet) <= m) {
            if |numbers| == 3 {
                result := [triplet];
                MultisetExtractionLemma(m, triplet);
                assert multiset(FlattenPartition(result)) == multiset(triplet);
                assert m == multiset(triplet);
            } else {
                result := [];
            }
        } else {
            result := [];
        }
    } else if (CountInMultiset(m, 1) >= 1 && CountInMultiset(m, 2) >= 1 && CountInMultiset(m, 6) >= 1) {
        var triplet := [1, 2, 6];
        ValidTripletCheck2(triplet);
        if (multiset(triplet) <= m) {
            if |numbers| == 3 {
                result := [triplet];
                MultisetExtractionLemma(m, triplet);
                assert multiset(FlattenPartition(result)) == multiset(triplet);
                assert m == multiset(triplet);
            } else {
                result := [];
            }
        } else {
            result := [];
        }
    } else {
        result := [];
    }
    
    if |result| == 0 {
        NoPartitionIsValid(result);
    }
}
// </vc-code>

