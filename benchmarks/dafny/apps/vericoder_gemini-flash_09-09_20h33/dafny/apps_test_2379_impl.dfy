predicate IsValidWorkSelection(N: int, K: int, C: int, S: string, selection: set<int>)
    requires |S| == N
{
    |selection| == K &&
    (forall day :: day in selection ==> 0 <= day < N && day < |S| && S[day] == 'o') &&
    (forall day1, day2 :: day1 in selection && day2 in selection && day1 != day2 ==> 
        day1 < day2 - C || day2 < day1 - C)
}

// <vc-helpers>
predicate IsValidWorkSelectionProperty(N: int, K: int, C: int, S: string, selection: set<int>)
    requires |S| == N
{
    |selection| == K &&
    (forall day :: day in selection ==> 0 <= day < N && day < |S| && S[day] == 'o') &&
    (forall day1, day2 :: day1 in selection && day2 in selection && day1 != day2 ==> 
        day1 < day2 - C || day2 < day1 - C)
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
    var currentSelection: seq<int> := [];
    var count: int := 0;
    var lastSelected: int := -C - 1; 

    for i := 0 to N - 1
        invariant 0 <= i <= N
        invariant 0 <= count <= K
        invariant forall k :: 0 <= k < |currentSelection| ==> 0 <= currentSelection[k] < N
        invariant forall k :: 0 <= k < |currentSelection| ==> S[currentSelection[k]] == 'o'
        invariant forall k, l :: 0 <= k < l < |currentSelection| ==> currentSelection[k] < currentSelection[l]
        invariant forall k, l :: 0 <= k < l < |currentSelection| ==> currentSelection[k] + C < currentSelection[l]
        invariant count == |currentSelection|
        invariant (count == 0 || lastSelected == currentSelection[count - 1])
        invariant (count == 0 || lastSelected >= -C - 1)
    {
        if count < K && S[i] == 'o' && i >= lastSelected + C + 1 {
            currentSelection := currentSelection + [i];
            lastSelected := i;
            count := count + 1;
        }
    }
    
    result := [];
    for i := 0 to |currentSelection| - 1
        decreases |currentSelection| - i
        invariant 0 <= i <= |currentSelection|
        invariant forall k :: 0 <= k < |result| ==> 1 <= result[k] <= N
        invariant forall k :: 0 <= k < |result| ==> S[result[k] - 1] == 'o'
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> result[k] == currentSelection[k] + 1
    {
        result := result + [currentSelection[i] + 1];
    }
}
// </vc-code>

