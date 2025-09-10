predicate IsValidWorkSelection(N: int, K: int, C: int, S: string, selection: set<int>)
    requires |S| == N
{
    |selection| == K &&
    (forall day :: day in selection ==> 0 <= day < N && day < |S| && S[day] == 'o') &&
    (forall day1, day2 :: day1 in selection && day2 in selection && day1 != day2 ==> 
        day1 < day2 - C || day2 < day1 - C)
}

// <vc-helpers>
// No additional helpers or proofs needed for this implementation
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
    var result: seq<int> := [];
    var pos := 0;
    while pos < N && result.Length < K
        invariant 0 <= pos <= N
        invariant result.Length <= K
        invariant forall i :: 0 <= i < result.Length ==> 1 <= result[i] <= N && S[result[i]-1] == 'o'
        invariant forall i :: 0 <= i < result.Length - 1 ==> result[i] < result[i + 1]
        invariant forall i :: 0 <= i < result.Length - 1 ==> result[i + 1] - result[i] >= C + 1
    {
        var d := pos;
        while d < N && S[d] != 'o'
            invariant pos <= d <= N
            invariant forall k :: pos <= k < d ==> S[k] != 'o'
        {
            d := d + 1;
        }
        if d < N {
            result := result + [d + 1];
            pos := d + C + 1;
        } else {
            pos := N;
        }
    }
    return result;
}
// </vc-code>

