function count_eligible(participations: seq<int>, k: int): int
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
{
    if |participations| == 0 then 0
    else (if 5 - participations[0] >= k then 1 else 0) + count_eligible(participations[1..], k)
}

// <vc-helpers>
lemma count_eligible_non_negative(participations: seq<int>, k: int)
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
    ensures count_eligible(participations, k) >= 0
{
    if |participations| == 0 {
    } else {
        count_eligible_non_negative(participations[1..], k);
    }
}

lemma count_eligible_extend(participations: seq<int>, k: int, i: int)
    requires 0 <= k <= 5
    requires 0 <= i < |participations|
    requires forall j :: 0 <= j < |participations| ==> 0 <= participations[j] <= 5
    ensures count_eligible(participations[..i+1], k) == 
            count_eligible(participations[..i], k) + (if 5 - participations[i] >= k then 1 else 0)
{
    assert participations[..i+1] == participations[..i] + [participations[i]];
    assert count_eligible(participations[..i+1], k) == 
           count_eligible(participations[..i], k) + count_eligible([participations[i]], k);
    assert count_eligible([participations[i]], k) == (if 5 - participations[i] >= k then 1 else 0);
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
    {
        if 5 - participations[i] >= k {
            count := count + 1;
        }
        count_eligible_extend(participations, k, i);
        i := i + 1;
    }
    
    assert i == |participations|;
    assert participations[..i] == participations;
    assert count == count_eligible(participations, k);
    count_eligible_non_negative(participations, k);
    result := count / 3;
}
// </vc-code>

