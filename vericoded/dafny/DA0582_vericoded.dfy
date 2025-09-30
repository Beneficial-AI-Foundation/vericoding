predicate ValidInput(n: int, a: int, b: int, k: int, H: seq<int>)
{
    n > 0 && a > 0 && b > 0 && k >= 0 && |H| == n && 
    forall i :: 0 <= i < |H| ==> H[i] > 0
}

function ProcessHealthValues(H: seq<int>, a: int, b: int): seq<int>
    requires a > 0 && b > 0
    requires forall i :: 0 <= i < |H| ==> H[i] > 0
    ensures |ProcessHealthValues(H, a, b)| == |H|
    ensures forall i :: 0 <= i < |H| ==> 
        var h_mod := H[i] % (a + b);
        ProcessHealthValues(H, a, b)[i] == (if h_mod == 0 then a + b else h_mod)
    ensures forall i :: 0 <= i < |ProcessHealthValues(H, a, b)| ==> 
        1 <= ProcessHealthValues(H, a, b)[i] <= a + b
{
    if |H| == 0 then []
    else 
        var h_mod := H[0] % (a + b);
        var h_final := if h_mod == 0 then a + b else h_mod;
        [h_final] + ProcessHealthValues(H[1..], a, b)
}

function CountKillableMonsters(sorted_health: seq<int>, a: int, k: int): int
    requires a > 0 && k >= 0
    requires forall i, j :: 0 <= i < j < |sorted_health| ==> sorted_health[i] <= sorted_health[j]
    requires forall i :: 0 <= i < |sorted_health| ==> sorted_health[i] > 0
    ensures 0 <= CountKillableMonsters(sorted_health, a, k) <= |sorted_health|
{
    CountKillableHelper(sorted_health, a, k, 0, 0)
}

function CountKillableHelper(sorted_health: seq<int>, a: int, remaining_k: int, index: int, acc: int): int
    requires a > 0 && remaining_k >= 0 && 0 <= index <= |sorted_health| && acc >= 0
    requires forall i, j :: 0 <= i < j < |sorted_health| ==> sorted_health[i] <= sorted_health[j]
    requires forall i :: 0 <= i < |sorted_health| ==> sorted_health[i] > 0
    ensures CountKillableHelper(sorted_health, a, remaining_k, index, acc) >= acc
    ensures CountKillableHelper(sorted_health, a, remaining_k, index, acc) <= acc + (|sorted_health| - index)
    decreases |sorted_health| - index
{
    if index >= |sorted_health| then acc
    else
        var x := sorted_health[index];
        if x <= a then
            CountKillableHelper(sorted_health, a, remaining_k, index + 1, acc + 1)
        else
            var needed_skips := (x + a - 1) / a - 1;
            if remaining_k >= needed_skips then
                CountKillableHelper(sorted_health, a, remaining_k - needed_skips, index + 1, acc + 1)
            else
                CountKillableHelper(sorted_health, a, remaining_k, index + 1, acc)
}

// <vc-helpers>
lemma ProcessHealthValuesProperties(H: seq<int>, a: int, b: int)
    requires a > 0 && b > 0
    requires forall i :: 0 <= i < |H| ==> H[i] > 0
    ensures var processed := ProcessHealthValues(H, a, b);
            |processed| == |H| &&
            (forall i :: 0 <= i < |processed| ==> 1 <= processed[i] <= a + b) &&
            (forall i :: 0 <= i < |processed| ==> processed[i] > 0)
{
    // This follows directly from the function's ensures clauses
    // The last property follows from 1 <= processed[i]
}

method SortSequence(s: seq<int>) returns (sorted: seq<int>)
    ensures |sorted| == |s|
    ensures multiset(sorted) == multiset(s)
    ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    ensures forall i :: 0 <= i < |s| ==> s[i] > 0 ==> exists j :: 0 <= j < |sorted| && sorted[j] == s[i]
    ensures forall i :: 0 <= i < |sorted| ==> exists j :: 0 <= j < |s| && sorted[i] == s[j]
{
    if |s| == 0 {
        sorted := [];
        return;
    }
    
    sorted := s;
    var i := 0;
    while i < |sorted|
        invariant 0 <= i <= |sorted|
        invariant |sorted| == |s|
        invariant multiset(sorted) == multiset(s)
        invariant forall j, k :: 0 <= j < k < i ==> sorted[j] <= sorted[k]
        invariant forall j, k :: 0 <= j < i <= k < |sorted| ==> sorted[j] <= sorted[k]
    {
        var minIndex := i;
        var j := i + 1;
        while j < |sorted|
            invariant i < j <= |sorted|
            invariant i <= minIndex < |sorted|
            invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
        {
            if sorted[j] < sorted[minIndex] {
                minIndex := j;
            }
            j := j + 1;
        }
        
        if minIndex != i {
            var temp := sorted[i];
            var before_swap := sorted;
            sorted := sorted[i := sorted[minIndex]][minIndex := temp];
            assert multiset(sorted) == multiset(before_swap);
        }
        i := i + 1;
    }
    
    // Prove the last two postconditions using multiset equality
    assert multiset(sorted) == multiset(s);
    forall i | 0 <= i < |s| && s[i] > 0
    ensures exists j :: 0 <= j < |sorted| && sorted[j] == s[i]
    {
        assert s[i] in multiset(s);
        assert s[i] in multiset(sorted);
        assert exists j :: 0 <= j < |sorted| && sorted[j] == s[i];
    }
    
    forall i | 0 <= i < |sorted|
    ensures exists j :: 0 <= j < |s| && sorted[i] == s[j]
    {
        assert sorted[i] in multiset(sorted);
        assert sorted[i] in multiset(s);
        assert exists j :: 0 <= j < |s| && s[j] == sorted[i];
    }
}

lemma MultisetPreservesPositive(s: seq<int>, sorted: seq<int>)
    requires multiset(sorted) == multiset(s)
    requires forall i :: 0 <= i < |s| ==> s[i] > 0
    ensures forall i :: 0 <= i < |sorted| ==> sorted[i] > 0
{
    forall i | 0 <= i < |sorted|
    ensures sorted[i] > 0
    {
        assert sorted[i] in multiset(sorted);
        assert sorted[i] in multiset(s);
        var j :| 0 <= j < |s| && s[j] == sorted[i];
        assert s[j] > 0;
    }
}
// </vc-helpers>

// <vc-spec>
method SolveCore(n: int, a: int, b: int, k: int, H: seq<int>) returns (result: int)
    requires ValidInput(n, a, b, k, H)
    ensures 0 <= result <= n
// </vc-spec>
// <vc-code>
{
    var processed := ProcessHealthValues(H, a, b);
    ProcessHealthValuesProperties(H, a, b);
    
    assert forall i :: 0 <= i < |processed| ==> processed[i] > 0;
    
    var sorted_health := SortSequence(processed);
    
    assert |sorted_health| == |processed|;
    assert multiset(sorted_health) == multiset(processed);
    
    MultisetPreservesPositive(processed, sorted_health);
    
    assert forall i :: 0 <= i < |sorted_health| ==> sorted_health[i] > 0;
    
    result := CountKillableMonsters(sorted_health, a, k);
}
// </vc-code>

