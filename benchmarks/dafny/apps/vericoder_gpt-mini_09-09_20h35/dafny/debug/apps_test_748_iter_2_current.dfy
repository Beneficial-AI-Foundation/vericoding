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
lemma FlattenPartition_multiset(result: seq<seq<int>>)
    requires forall i :: 0 <= i < |result| ==> |result[i]| == 3
    ensures multiset(FlattenPartition(result)) ==
            if |result| == 0 then multiset([]) else multiset(result[0]) + multiset(FlattenPartition(result[1..]))
{
    if |result| == 0 {
        // trivial
    } else {
        // By definition FlattenPartition(result) == result[0] + FlattenPartition(result[1..])
        // and multiset distributes over sequence concatenation.
    }
}

lemma FlattenPartition_prepend(t: seq<int>, rest: seq<seq<int>>)
    requires |t| == 3
    requires forall i :: 0 <= i < |rest| ==> |rest[i]| == 3
    ensures multiset(FlattenPartition([t] + rest)) == multiset(t) + multiset(FlattenPartition(rest))
{
    // By definition FlattenPartition([t] + rest) == t + FlattenPartition(rest)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, numbers: seq<int>) returns (result: seq<seq<int>>)
    requires ValidInput(n, numbers)
    ensures NoPartitionExists(result) || ValidPartition(result, numbers)
// </vc-spec>
// <vc-code>
{
    // Count occurrences of each number 1..7
    var cnt := new int[8];
    var i := 0;
    while i < |numbers|
        decreases |numbers| - i
    {
        cnt[numbers[i]] := cnt[numbers[i]] + 1;
        i := i + 1;
    }

    // If any impossible numbers appear, return empty (NoPartitionExists)
    if cnt[5] > 0 || cnt[7] > 0 {
        result := [];
        return;
    }

    // Each triplet must contain exactly one '1'
    var ones := cnt[1];
    if ones * 3 != n {
        result := [];
        return;
    }

    // Prepare result and ghost multisets to track used/remaining elements
    var res: seq<seq<int>> := [];
    ghost var collected: multiset<int> := multiset([]);
    ghost var rem: multiset<int> := multiset(numbers);

    // Process all 4s -> each 4 must be in a (1,2,4)
    var orig4 := cnt[4];
    i := 0;
    while i < orig4
        invariant 0 <= i <= orig4
        invariant collected == multiset(FlattenPartition(res))
        invariant rem + collected == multiset(numbers)
        decreases orig4 - i
    {
        if cnt[1] == 0 || cnt[2] == 0 {
            result := [];
            return;
        }
        var t := [1,2,4];
        assert ValidTriplet(t);
        // prepend to make FlattenPartition update easy to reason about
        res := [t] + res;
        // update counts
        cnt[1] := cnt[1] - 1;
        cnt[2] := cnt[2] - 1;
        cnt[4] := cnt[4] - 1;
        // update ghost multisets
        collected := collected + multiset(t);
        rem := rem - multiset(t);
        // use lemma to justify collected corresponds to FlattenPartition(res)
        assert multiset(FlattenPartition(res)) == multiset(t) + multiset(FlattenPartition(res[1..])) by {
            // By definition and FlattenPartition_prepend
        }
        i := i + 1;
    }

    // Process all 3s -> each 3 must be in a (1,3,6)
    var orig3 := cnt[3];
    i := 0;
    while i < orig3
        invariant 0 <= i <= orig3
        invariant collected == multiset(FlattenPartition(res))
        invariant rem + collected == multiset(numbers)
        decreases orig3 - i
    {
        if cnt[1] == 0 || cnt[6] == 0 {
            result := [];
            return;
        }
        var t := [1,3,6];
        assert ValidTriplet(t);
        res := [t] + res;
        cnt[1] := cnt[1] - 1;
        cnt[3] := cnt[3] - 1;
        cnt[6] := cnt[6] - 1;
        collected := collected + multiset(t);
        rem := rem - multiset(t);
        i := i + 1;
    }

    // Remaining 2s must be paired as (1,2,6)
    var rem2 := cnt[2];
    i := 0;
    while i < rem2
        invariant 0 <= i <= rem2
        invariant collected == multiset(FlattenPartition(res))
        invariant rem + collected == multiset(numbers)
        decreases rem2 - i
    {
        if cnt[1] == 0 || cnt[6] == 0 {
            result := [];
            return;
        }
        var t := [1,2,6];
        assert ValidTriplet(t);
        res := [t] + res;
        cnt[1] := cnt[1] - 1;
        cnt[2] := cnt[2] - 1;
        cnt[6] := cnt[6] - 1;
        collected := collected + multiset(t);
        rem := rem - multiset(t);
        i := i + 1;
    }

    // After constructing, no leftover usable numbers should remain
    if cnt[1] != 0 || cnt[2] != 0 || cnt[3] != 0 || cnt[4] != 0 || cnt[6] != 0 {
        result := [];
        return;
    }

    // Now collected == multiset(numbers) because rem + collected == multiset(numbers) and rem should be empty
    assert collected == multiset(FlattenPartition(res)) by {
        // maintained invariant
    }
    assert rem + collected == multiset(numbers);
    assert rem == multiset([]);
    assert collected == multiset(numbers);

    // Number of triplets equals original number of ones which equals n/3
    assert |res| == ones;
    assert ones * 3 == n;
    assert |res| == n / 3;

    // All inner sequences are valid triplets (we asserted each when created)
    var j := 0;
    while j < |res|
        decreases |res| - j
    {
        assert ValidTriplet(res[j]);
        j := j + 1;
    }

    // Conclude ValidPartition
    assert ValidPartition(res, numbers);
    result := res;
    return;
}
// </vc-code>

