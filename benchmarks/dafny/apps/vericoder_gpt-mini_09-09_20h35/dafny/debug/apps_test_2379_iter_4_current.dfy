predicate IsValidWorkSelection(N: int, K: int, C: int, S: string, selection: set<int>)
    requires |S| == N
{
    |selection| == K &&
    (forall day :: day in selection ==> 0 <= day < N && day < |S| && S[day] == 'o') &&
    (forall day1, day2 :: day1 in selection && day2 in selection && day1 != day2 ==> 
        day1 < day2 - C || day2 < day1 - C)
}

// <vc-helpers>
// No helper code needed.
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
  var selection : set<int> :| IsValidWorkSelection(N, K, C, S, selection);

  var res0: seq<int> := [];
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall idx :: 0 <= idx < |res0| ==> res0[idx] in selection && 0 <= res0[idx] < i
    invariant forall a,b :: 0 <= a < b < |res0| ==> res0[a] < res0[b]
    invariant forall x :: x in selection && x < i ==> (exists idx :: 0 <= idx < |res0| && res0[idx] == x)
    invariant |res0| <= |selection|
    decreases N - i
  {
    i := i + 1;
    if i - 1 in selection {
      res0 := res0 + [i - 1];
    }
  }

  assert i == N;
  assert forall idx :: 0 <= idx < |res0| ==> res0[idx] in selection;
  assert forall x :: x in selection ==> exists idx :: 0 <= idx < |res0| && res0[idx] == x;
  assert |res0| == |selection|;

  var res1: seq<int> := [];
  var j := 0;
  while j < |res0|
    invariant 0 <= j <= |res0|
    invariant forall idx :: 0 <= idx < |res1| ==> 1 <= res1[idx] <= N
    invariant forall a,b :: 0 <= a < b < |res1| ==> res1[a] < res1[b]
    invariant |res1| == j
    invariant forall k :: 0 <= k < |res1| ==> res1[k] == res0[k] + 1
    decreases |res0| - j
  {
    j := j + 1;
    res1 := res1 + [res0[j - 1] + 1];
  }

  assert |res1| == |res0|;
  assert forall idx :: 0 <= idx < |res1| ==> 1 <= res1[idx] <= N;
  assert forall idx :: 0 <= idx < |res1| ==> S[res1[idx] - 1] == 'o';
  assert forall a,b :: 0 <= a < b < |res1| ==> res1[a] < res1[b];
  assert |res1| <= K;

  result := res1;
}
// </vc-code>

