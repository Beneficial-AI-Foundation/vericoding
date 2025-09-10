function count_eligible(participations: seq<int>, k: int): int
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
{
    if |participations| == 0 then 0
    else (if 5 - participations[0] >= k then 1 else 0) + count_eligible(participations[1..], k)
}

// <vc-helpers>
lemma count_eligible_tail_recursive(participations: seq<int>, k: int, acc: int) returns (total: int)
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
    requires acc >= 0
    ensures total == acc + count_eligible(participations, k)
    decreases |participations|
{
    if |participations| == 0 {
        total := acc;
    } else {
        var new_acc := acc + (if 5 - participations[0] >= k then 1 else 0);
        total := count_eligible_tail_recursive(participations[1..], k, new_acc);
    }
}

lemma division_property(x: int, d: int)
    requires x >= 0 && d > 0
    ensures x / d >= 0
{
}

lemma count_eligible_empty(k: int)
    requires 0 <= k <= 5
    ensures count_eligible([], k) == 0
{
}

lemma count_eligible_slice_property_recursive(participations: seq<int>, k: int)
    requires 0 <= k <= 5
    requires forall j :: 0 <= j < |participations| ==> 0 <= participations[j] <= 5
    ensures count_eligible(participations, k) == (if |participations| == 0 then 0 else (if 5 - participations[0] >= k then 1 else 0) + count_eligible(participations[1..], k))
{
}

lemma count_eligible_slice_property(participations: seq<int>, k: int, i: int)
    requires 0 <= k <= 5
    requires forall j :: 0 <= j < |participations| ==> 0 <= participations[j] <= 5
    requires 0 <= i <= |participations|
    ensures count_eligible(participations[..i], k) + count_eligible(participations[i..], k) == count_eligible(participations, k)
    decreases |participations|
{
    if i == 0 {
        assert participations[0..] == participations;
        assert participations[..0] == [];
        count_eligible_empty(k);
    } else if i == |participations| {
        assert participations[..i] == participations;
        assert participations[i..] == [];
        count_eligible_empty(k);
    } else {
        var head := participations[..i];
        var tail := participations[i..];
        
        // Recursive case: split at i-1 instead
        count_eligible_slice_property(participations, k, i-1);
        
        var head_minus_last := participations[..i-1];
        var last_elem := participations[i-1];
        var tail_plus_last := participations[i-1..];
        
        assert head == head_minus_last + [last_elem];
        assert tail_plus_last == [last_elem] + tail;
        
        // Prove the relationship between the slices
        count_eligible_slice_property_recursive(head, k);
        count_eligible_slice_property_recursive(tail_plus_last, k);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, participations: seq<int>) returns (result: int)
    requires 0 <= k <= 5
    requires n == |participations|
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
    ensures result == (count_eligible(participations, k) / 3)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var count := 0;
    var i := 0;
    while i < |participations|
        invariant 0 <= i <= |participations|
        invariant count == count_eligible(participations[..i], k)
        decreases |participations| - i
    {
        if 5 - participations[i] >= k {
            count := count + 1;
        }
        i := i + 1;
    }
    count_eligible_slice_property(participations, k, i);
    assert count == count_eligible(participations, k);
    division_property(count, 3);
    result := count / 3;
}
// </vc-code>

