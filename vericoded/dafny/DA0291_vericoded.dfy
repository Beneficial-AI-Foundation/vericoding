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
        assert count_eligible(participations, k) == 0;
    } else {
        count_eligible_non_negative(participations[1..], k);
        assert count_eligible(participations[1..], k) >= 0;
        assert count_eligible(participations, k) == 
               (if 5 - participations[0] >= k then 1 else 0) + count_eligible(participations[1..], k);
        assert (if 5 - participations[0] >= k then 1 else 0) >= 0;
    }
}

lemma count_eligible_append(participations: seq<int>, k: int, index: int)
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
    requires 0 <= index < |participations|
    ensures count_eligible(participations[..index+1], k) == 
            count_eligible(participations[..index], k) + (if 5 - participations[index] >= k then 1 else 0)
{
    var s := participations[..index];
    var elem := participations[index];
    assert participations[..index+1] == s + [elem];
    
    count_eligible_append_helper(s, elem, k);
}

lemma count_eligible_append_helper(s: seq<int>, elem: int, k: int)
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 5
    requires 0 <= elem <= 5
    ensures count_eligible(s + [elem], k) == count_eligible(s, k) + (if 5 - elem >= k then 1 else 0)
{
    if |s| == 0 {
        assert s + [elem] == [elem];
        assert count_eligible([elem], k) == (if 5 - elem >= k then 1 else 0);
        assert count_eligible(s, k) == 0;
    } else {
        assert (s + [elem])[0] == s[0];
        assert (s + [elem])[1..] == s[1..] + [elem];
        
        count_eligible_append_helper(s[1..], elem, k);
        
        assert count_eligible(s + [elem], k) == 
               (if 5 - s[0] >= k then 1 else 0) + count_eligible(s[1..] + [elem], k);
        assert count_eligible(s[1..] + [elem], k) == 
               count_eligible(s[1..], k) + (if 5 - elem >= k then 1 else 0);
        assert count_eligible(s, k) == 
               (if 5 - s[0] >= k then 1 else 0) + count_eligible(s[1..], k);
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
    var eligible_count := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant eligible_count == count_eligible(participations[..i], k)
        invariant eligible_count >= 0
    {
        count_eligible_append(participations, k, i);
        if 5 - participations[i] >= k {
            eligible_count := eligible_count + 1;
        }
        i := i + 1;
    }
    
    assert i == n;
    assert participations[..n] == participations;
    assert eligible_count == count_eligible(participations, k);
    count_eligible_non_negative(participations, k);
    assert count_eligible(participations, k) >= 0;
    assert eligible_count >= 0;
    
    result := eligible_count / 3;
    assert result >= 0;
}
// </vc-code>

