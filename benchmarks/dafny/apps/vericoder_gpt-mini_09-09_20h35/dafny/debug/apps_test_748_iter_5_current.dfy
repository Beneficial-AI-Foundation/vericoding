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
    if |rest| == 0 {
        // trivial
    } else {
        FlattenPartition_multiset([t] + rest);
    }
}

lemma FlattenPartition_length(result: seq<seq<int>>)
    requires forall i :: 0 <= i < |result| ==> |result[i]| == 3
    ensures |FlattenPartition(result)| == 3 * |result|
{
    if |result| == 0 {
        // trivial
    } else {
        FlattenPartition_length(result[1..]);
        // FlattenPartition(result) == result[0] + FlattenPartition(result[1..])
        // so length = 3 + 3*(|result|-1) = 3*|result|
    }
}

lemma Multiset_add_cardinality<A>(m1: multiset<A>, m2: multiset<A>)
    ensures |m1 + m2| == |m1| + |m2|
{
    // Follows from definition of multiset addition.
}

lemma Multiset_card_zero_empty<A>(m: multiset<A>)
    ensures |m| == 0 ==> m == multiset([])
{
    // If a multiset has zero cardinality it is the empty multiset.
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
    ghost var usedOnes := 0;

    // Process all 4s -> each 4 must be in a (1,2,4)
    var orig4 := cnt[4];
    assert 0 <= orig4;
    i := 0;
    assert 0 <= i <= orig4;
    while i < orig4
        invariant 0 <= i <= orig4
        invariant collected == multiset(FlattenPartition(res))
        invariant rem + collected == multiset(numbers)
        invariant forall k :: 0 <= k < |res| ==> |res[k]| == 3
        invariant |res| == usedOnes
        invariant usedOnes + cnt[1] == ones
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
        usedOnes := usedOnes + 1;
        // use lemma to justify collected corresponds to FlattenPartition(res)
        FlattenPartition_prepend(t, res[1..]);
        assert collected == multiset(FlattenPartition(res));
        // re-establish other invariants for the verifier
        assert rem + collected == multiset(numbers);
        assert |res| == usedOnes;
        assert usedOnes + cnt[1] == ones;
        i := i + 1;
    }

    // Process all 3s -> each 3 must be in a (1,3,6)
    var orig3 := cnt[3];
    assert 0 <= orig3;
    i := 0;
    assert 0 <= i <= orig3;
    while i < orig3
        invariant 0 <= i <= orig3
        invariant collected == multiset(FlattenPartition(res))
        invariant rem + collected == multiset(numbers)
        invariant forall k :: 0 <= k < |res| ==> |res[k]| == 3
        invariant |res| == usedOnes
        invariant usedOnes + cnt[1] == ones
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
        usedOnes := usedOnes + 1;
        FlattenPartition_prepend(t, res[1..]);
        assert collected == multiset(FlattenPartition(res));
        // re-establish other invariants for the verifier
        assert rem + collected == multiset(numbers);
        assert |res| == usedOnes;
        assert usedOnes + cnt[1] == ones;
        i := i + 1;
    }

    // Remaining 2s must be paired as (1,2,6)
    var rem2 := cnt[2];
    assert 0 <= rem2;
    i := 0;
    assert 0 <= i <= rem2;
    while i < rem2
        invariant 0 <= i <= rem2
        invariant collected == multiset(FlattenPartition(res))
        invariant rem + collected == multiset(numbers)
        invariant forall k :: 0 <= k < |res| ==> |res[k]| == 3
        invariant |res| == usedOnes
        invariant usedOnes + cnt[1] == ones
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
        usedOnes := usedOnes + 1;
        FlattenPartition_prepend(t, res[1..]);
        assert collected == multiset(FlattenPartition(res));
        // re-establish other invariants for the verifier
        assert rem + collected == multiset(numbers);
        assert |res| == usedOnes;
        assert usedOnes + cnt[1] == ones;
        i := i + 1;
    }

    // After constructing, no leftover usable numbers should remain
    if cnt[1] != 0 || cnt[2] != 0 || cnt[3] != 0 || cnt[4] != 0 || cnt[6] != 0 {
        result := [];
        return;
    }

    // Now prove collected == multiset(numbers) by cardinality arguments
    assert collected == multiset(FlattenPartition(res)) by {
        // maintained invariant
    }
    assert rem + collected == multiset(numbers);
    // Use FlattenPartition length lemma to relate counts
    FlattenPartition_length(res);
    assert |FlattenPartition(res)| == 3 * |res|;
    // from invariants usedOnes + cnt[1] == ones and cnt[1]==0 and |res|==usedOnes we get |res| == ones
    assert |res| == usedOnes;
    assert usedOnes + cnt[1] == ones;
    assert cnt[1] == 0;
    assert |res| == ones;
    assert ones * 3 == n;
    assert |numbers| == n;
    assert |FlattenPartition(res)| == |numbers|;
    // cardinality of multisets: |collected + rem| == |collected| + |rem|
    Multiset_add_cardinality(collected, rem);
    assert |multiset(numbers)| == |collected| + |rem|;
    // |multiset(numbers)| == |numbers|
    assert |multiset(numbers)| == |numbers|;
    // substitute |collected| == |FlattenPartition(res)| and that equals |numbers|
    assert |collected| == |FlattenPartition(res)|;
    assert |collected| == |numbers|;
    // hence |rem| == 0
    assert |rem| == 0;
    // so rem is empty multiset
    Multiset_card_zero_empty(rem);
    assert rem == multiset([]);
    assert collected == multiset(numbers);

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

