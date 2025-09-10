predicate IsValidWorkSelection(N: int, K: int, C: int, S: string, selection: set<int>)
    requires |S| == N
{
    |selection| == K &&
    (forall day :: day in selection ==> 0 <= day < N && day < |S| && S[day] == 'o') &&
    (forall day1, day2 :: day1 in selection && day2 in selection && day1 != day2 ==> 
        day1 < day2 - C || day2 < day1 - C)
}

// <vc-helpers>
lemma SubsetPreservesValidSelection(N: int, K: int, C: int, S: string, selection: set<int>, subset: set<int>)
    requires |S| == N
    requires IsValidWorkSelection(N, K, C, S, selection)
    requires subset <= selection
    ensures forall day :: day in subset ==> 0 <= day < N && S[day] == 'o'
    ensures forall day1, day2 :: day1 in subset && day2 in subset && day1 != day2 ==> 
        day1 < day2 - C || day2 < day1 - C
{
}

lemma ValidSelectionExists(N: int, K: int, C: int, S: string)
    requires N > 0 && K > 0 && C >= 0 && K <= N
    requires |S| == N
    requires forall i :: 0 <= i < |S| ==> S[i] == 'o' || S[i] == 'x'
    requires |set i | 0 <= i < |S| && S[i] == 'o'| >= K
    requires exists validSelection :: IsValidWorkSelection(N, K, C, S, validSelection)
    ensures exists selection: set<int> :: IsValidWorkSelection(N, K, C, S, selection)
{
    var validSelection :| IsValidWorkSelection(N, K, C, S, validSelection);
}

lemma SetCardinalityIncrease(s: set<int>, j: int, bound: int)
    requires 0 <= j < bound
    requires j in s
    requires forall day :: day in s ==> 0 <= day < bound
    ensures |set day | day in s && day < j + 1| == |set day | day in s && day < j| + 1
{
    var setBefore := set day | day in s && day < j;
    var setAfter := set day | day in s && day < j + 1;
    assert setAfter == setBefore + {j};
    assert j !in setBefore;
}

lemma SetCardinalityMaintained(s: set<int>, j: int, bound: int)
    requires 0 <= j < bound
    requires j !in s
    requires forall day :: day in s ==> 0 <= day < bound
    ensures |set day | day in s && day < j + 1| == |set day | day in s && day < j|
{
    var setBefore := set day | day in s && day < j;
    var setAfter := set day | day in s && day < j + 1;
    assert setAfter == setBefore;
}

lemma SetCardinalityBound(s: set<int>, j: int, bound: int)
    requires 0 <= j <= bound
    requires forall day :: day in s ==> 0 <= day < bound
    ensures |set day | day in s && day < j| <= |s|
{
    var subset := set day | day in s && day < j;
    assert subset <= s;
}

lemma AllSelectedLessThanN(s: set<int>, N: int)
    requires forall day :: day in s ==> 0 <= day < N
    ensures set day | day in s && day < N == s
{
    assert forall day :: day in s ==> day < N;
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, K: int, C: int, S: string) returns (result: seq<int>)
    requires N > 0
    requires K > 0
    requires C >= 0
    requires K <= N
    requires |S| == N
    requires forall i :: 0 <= i < |S| ==> S[i] == 'o' || S[i] == 'x'
    requires |set i | 0 <= i < |S| && S[i] == 'o'| >= K
    requires exists validSelection :: IsValidWorkSelection(N, K, C, S, validSelection)
    ensures forall i :: 0 <= i < |result| ==> 1 <= result[i] <= N
    ensures forall i :: 0 <= i < |result| ==> S[result[i] - 1] == 'o'
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures |result| <= K
// </vc-spec>
// <vc-code>
{
    var selected := {};
    var i := 0;
    var lastSelected := -C - 1;
    
    while i < N && |selected| < K
        invariant 0 <= i <= N
        invariant |selected| <= K
        invariant forall day :: day in selected ==> 0 <= day < i && S[day] == 'o'
        invariant forall day :: day in selected ==> 0 <= day < N
        invariant forall day1, day2 :: day1 in selected && day2 in selected && day1 != day2 ==> 
            day1 < day2 - C || day2 < day1 - C
        invariant lastSelected in selected || lastSelected == -C - 1
        invariant lastSelected == -C - 1 || (lastSelected in selected && 
            forall day :: day in selected ==> day <= lastSelected)
        invariant forall day :: day in selected && day != lastSelected ==> day < lastSelected - C
    {
        if S[i] == 'o' && i > lastSelected + C {
            selected := selected + {i};
            lastSelected := i;
        }
        i := i + 1;
    }
    
    // Convert set to sorted sequence with 1-based indexing
    var selectedSeq: seq<int> := [];
    var j := 0;
    
    AllSelectedLessThanN(selected, N);
    assert set day | day in selected && day < N == selected;
    
    while j < N
        invariant 0 <= j <= N
        invariant forall day :: day in selected ==> 0 <= day < N
        invariant |selectedSeq| == |set day | day in selected && day < j|
        invariant |selectedSeq| <= |selected|
        invariant forall k :: 0 <= k < |selectedSeq| ==> 1 <= selectedSeq[k] <= N
        invariant forall k :: 0 <= k < |selectedSeq| ==> S[selectedSeq[k] - 1] == 'o'
        invariant forall k1, k2 :: 0 <= k1 < k2 < |selectedSeq| ==> selectedSeq[k1] < selectedSeq[k2]
        invariant forall k :: 0 <= k < |selectedSeq| ==> selectedSeq[k] - 1 in selected && selectedSeq[k] - 1 < j
    {
        if j in selected {
            SetCardinalityBound(selected, j, N);
            SetCardinalityIncrease(selected, j, N);
            selectedSeq := selectedSeq + [j + 1];
        } else {
            SetCardinalityBound(selected, j, N);
            SetCardinalityMaintained(selected, j, N);
        }
        j := j + 1;
    }
    
    AllSelectedLessThanN(selected, N);
    assert set day | day in selected && day < N == selected;
    assert |selectedSeq| == |selected|;
    assert |selected| <= K;
    assert |selectedSeq| <= K;
    
    result := selectedSeq;
}
// </vc-code>

