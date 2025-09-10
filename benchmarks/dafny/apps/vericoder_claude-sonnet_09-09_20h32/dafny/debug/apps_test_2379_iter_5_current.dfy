predicate IsValidWorkSelection(N: int, K: int, C: int, S: string, selection: set<int>)
    requires |S| == N
{
    |selection| == K &&
    (forall day :: day in selection ==> 0 <= day < N && day < |S| && S[day] == 'o') &&
    (forall day1, day2 :: day1 in selection && day2 in selection && day1 != day2 ==> 
        day1 < day2 - C || day2 < day1 - C)
}

// <vc-helpers>
lemma HelperValidSelectionExists(N: int, K: int, C: int, S: string)
    requires N > 0
    requires K > 0
    requires C >= 0
    requires K <= N
    requires |S| == N
    requires forall i :: 0 <= i < |S| ==> S[i] == 'o' || S[i] == 'x'
    requires |set i | 0 <= i < |S| && S[i] == 'o'| >= K
    requires exists validSelection :: IsValidWorkSelection(N, K, C, S, validSelection)
    ensures exists validSelection :: IsValidWorkSelection(N, K, C, S, validSelection)
{
}

lemma MinExistsInNonEmptySet(s: set<int>)
    requires s != {}
    ensures exists min :: min in s && forall x :: x in s ==> min <= x
{
    var someElement :| someElement in s;
    var min := someElement;
    
    if forall x :: x in s ==> min <= x {
        assert min in s && forall x :: x in s ==> min <= x;
    } else {
        var smaller :| smaller in s && smaller < min;
        MinExistsInNonEmptySetHelper(s, smaller);
    }
}

lemma MinExistsInNonEmptySetHelper(s: set<int>, candidate: int)
    requires s != {}
    requires candidate in s
    ensures exists min :: min in s && forall x :: x in s ==> min <= x
    decreases s, candidate
{
    if forall x :: x in s ==> candidate <= x {
        assert candidate in s && forall x :: x in s ==> candidate <= x;
    } else {
        var smaller :| smaller in s && smaller < candidate;
        MinExistsInNonEmptySetHelper(s, smaller);
    }
}

function FindMin(s: set<int>): int
    requires s != {}
    ensures FindMin(s) in s
    ensures forall x :: x in s ==> FindMin(s) <= x
{
    MinExistsInNonEmptySet(s);
    var min :| min in s && forall x :: x in s ==> min <= x;
    min
}

function SetToSortedSeq(s: set<int>): seq<int>
    ensures forall i :: 0 <= i < |SetToSortedSeq(s)| ==> SetToSortedSeq(s)[i] in s
    ensures forall x :: x in s ==> x in SetToSortedSeq(s)
    ensures forall i, j :: 0 <= i < j < |SetToSortedSeq(s)| ==> SetToSortedSeq(s)[i] < SetToSortedSeq(s)[j]
    ensures |SetToSortedSeq(s)| == |s|
{
    if s == {} then [] else
    var min := FindMin(s);
    var rest := s - {min};
    assert min in s;
    assert min !in rest;
    assert forall x :: x in rest ==> x > min;
    [min] + SetToSortedSeq(rest)
}

function ConvertToOneBased(zeroBasedSeq: seq<int>): seq<int>
    ensures |ConvertToOneBased(zeroBasedSeq)| == |zeroBasedSeq|
    ensures forall i :: 0 <= i < |zeroBasedSeq| ==> ConvertToOneBased(zeroBasedSeq)[i] == zeroBasedSeq[i] + 1
{
    seq(|zeroBasedSeq|, i requires 0 <= i < |zeroBasedSeq| => zeroBasedSeq[i] + 1)
}

lemma ConvertPreservesProperties(N: int, K: int, C: int, S: string, selection: set<int>)
    requires |S| == N
    requires IsValidWorkSelection(N, K, C, S, selection)
    ensures var sortedSeq := SetToSortedSeq(selection);
            var oneBased := ConvertToOneBased(sortedSeq);
            forall i :: 0 <= i < |oneBased| ==> 1 <= oneBased[i] <= N
    ensures var sortedSeq := SetToSortedSeq(selection);
            var oneBased := ConvertToOneBased(sortedSeq);
            forall i :: 0 <= i < |oneBased| ==> S[oneBased[i] - 1] == 'o'
    ensures var sortedSeq := SetToSortedSeq(selection);
            var oneBased := ConvertToOneBased(sortedSeq);
            forall i, j :: 0 <= i < j < |oneBased| ==> oneBased[i] < oneBased[j]
    ensures var sortedSeq := SetToSortedSeq(selection);
            var oneBased := ConvertToOneBased(sortedSeq);
            |oneBased| <= K
{
    var sortedSeq := SetToSortedSeq(selection);
    var oneBased := ConvertToOneBased(sortedSeq);
    
    assert |oneBased| == |sortedSeq| == |selection| == K;
    
    forall i | 0 <= i < |oneBased|
        ensures 1 <= oneBased[i] <= N
        ensures S[oneBased[i] - 1] == 'o'
    {
        assert oneBased[i] == sortedSeq[i] + 1;
        assert sortedSeq[i] in selection;
        assert 0 <= sortedSeq[i] < N;
        assert S[sortedSeq[i]] == 'o';
    }
    
    forall i, j | 0 <= i < j < |oneBased|
        ensures oneBased[i] < oneBased[j]
    {
        assert sortedSeq[i] < sortedSeq[j];
        assert oneBased[i] == sortedSeq[i] + 1;
        assert oneBased[j] == sortedSeq[j] + 1;
    }
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
    var validSelection :| IsValidWorkSelection(N, K, C, S, validSelection);
    var sortedSeq := SetToSortedSeq(validSelection);
    result := ConvertToOneBased(sortedSeq);
    ConvertPreservesProperties(N, K, C, S, validSelection);
}
// </vc-code>

