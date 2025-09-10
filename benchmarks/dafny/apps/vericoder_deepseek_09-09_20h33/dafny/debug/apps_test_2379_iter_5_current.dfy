predicate IsValidWorkSelection(N: int, K: int, C: int, S: string, selection: set<int>)
    requires |S| == N
{
    |selection| == K &&
    (forall day :: day in selection ==> 0 <= day < N && day < |S| && S[day] == 'o') &&
    (forall day1, day2 :: day1 in selection && day2 in selection && day1 != day2 ==> 
        day1 < day2 - C || day2 < day1 - C)
}

// <vc-helpers>
predicate IsValidWorkSelection0(N: int, K: int, C: int, S: string, selection: set<int>)
    requires |S| == N
{
    |selection| == K &&
    (forall day :: day in selection ==> 0 <= day < N && day < |S| && S[day] == 'o') &&
    (forall day1, day2 :: day1 in selection && day2 in selection && day1 != day2 ==> 
        day1 < day2 - C || day2 < day1 - C)
}

lemma {:vcs_split_on_every_assert} IterateToFindSelection(N: int, K: int, C: int, S: string, 
  selection: set<int>, day: int)
  requires |S| == N
  requires IsValidWorkSelection0(N, K, C, S, selection)
  requires 0 <= day < N
  requires S[day] == 'o'
  ensures exists sel :: IsValidWorkSelection0(N, K, C, S, sel) && day in sel
{
}

lemma {:vcs_split_on_every_assert} ExtendSelection(N: int, K: int, C: int, S: string, 
  selection: set<int>, day: int) returns (extended: set<int>)
  requires |S| == N
  requires IsValidWorkSelection0(N, K, C, S, selection)
  requires 0 <= day < N && S[day] == 'o'
  requires !(day in selection)
  requires forall d :: d in selection ==> day < d - C || d < day - C
  ensures IsValidWorkSelection0(N, K+1, C, S, extended) && day in extended
{
  extended := selection + {day};
}

function max(a: int, b: int): int {
  if a >= b then a else b
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
  var resultSeq: seq<int> := [];
  var lastWorkDay := -C - 1;
  var workDaysFound := 0;
  var day := 0;
  
  while (workDaysFound < K)
    invariant 0 <= workDaysFound <= K
    invariant -C - 1 <= lastWorkDay < N
    invariant forall i :: 0 <= i < |resultSeq| ==> 1 <= resultSeq[i] <= N
    invariant forall i :: 0 <= i < |resultSeq| ==> S[resultSeq[i] - 1] == 'o'
    invariant forall i, j :: 0 <= i < j < |resultSeq| ==> resultSeq[i] < resultSeq[j]
    invariant |resultSeq| == workDaysFound
    invariant day <= N
    decreases K - workDaysFound
  {
    var found := false;
    var nextDay := max(lastWorkDay + C + 1, 0);
    
    while (nextDay < N && !found)
      invariant lastWorkDay + C + 1 <= nextDay <= N
      invariant forall d :: lastWorkDay + C + 1 <= d < nextDay ==> d < N ==> S[d] != 'o'
      decreases N - nextDay
    {
      if (S[nextDay] == 'o') {
        resultSeq := resultSeq + [nextDay + 1];
        lastWorkDay := nextDay;
        workDaysFound := workDaysFound + 1;
        found := true;
      }
      nextDay := nextDay + 1;
    }
    
    if (!found) {
      break;
    }
  }
  
  result := resultSeq;
}
// </vc-code>

