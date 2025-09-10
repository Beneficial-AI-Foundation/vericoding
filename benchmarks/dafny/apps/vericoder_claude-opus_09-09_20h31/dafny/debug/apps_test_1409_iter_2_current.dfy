function count_eligible(participations: seq<int>, k: int): int
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
{
    if |participations| == 0 then 0
    else (if 5 - participations[0] >= k then 1 else 0) + count_eligible(participations[1..], k)
}

// <vc-helpers>
lemma count_eligible_lemma(participations: seq<int>, k: int, index: int, count: int)
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
    requires 0 <= index <= |participations|
    requires count == count_eligible(participations[..index], k)
    ensures count >= 0
{
    if index == 0 {
        assert participations[..0] == [];
        assert count_eligible([], k) == 0;
    } else {
        var prev_count := count_eligible(participations[..index-1], k);
        assert participations[..index] == participations[..index-1] + [participations[index-1]];
        assert count == prev_count + (if 5 - participations[index-1] >= k then 1 else 0);
        count_eligible_lemma(participations, k, index - 1, prev_count);
    }
}

lemma count_eligible_append(participations: seq<int>, k: int, index: int)
    requires 0 <= k <= 5
    requires forall i :: 0 <= i < |participations| ==> 0 <= participations[i] <= 5
    requires 0 <= index < |participations|
    ensures count_eligible(participations[..index+1], k) == 
            count_eligible(participations[..index], k) + (if 5 - participations[index] >= k then 1 else 0)
{
    assert participations[..index+1] == participations[..index] + [participations[index]];
    
    var s := participations[..index];
    var elem := participations[index];
    
    assert count_eligible(s + [elem], k) == 
           (if |s + [elem]| == 0 then 0 
            else (if 5 - (s + [elem])[0] >= k then 1 else 0) + count_eligible((s + [elem])[1..], k));
    
    if |s| == 0 {
        assert s + [elem] == [elem];
        assert count_eligible([elem], k) == (if 5 - elem >= k then 1 else 0);
        assert count_eligible(s, k) == 0;
    } else {
        assert (s + [elem])[0] == s[0];
        assert (s + [elem])[1..] == s[1..] + [elem];
        assert count_eligible(s + [elem], k) == 
               (if 5 - s[0] >= k then 1 else 0) + count_eligible(s[1..] + [elem], k);
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
    count_eligible_lemma(participations, k, n, eligible_count);
    
    result := eligible_count / 3;
}
// </vc-code>

