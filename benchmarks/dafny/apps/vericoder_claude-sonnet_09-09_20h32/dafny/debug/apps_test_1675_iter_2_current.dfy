predicate ValidInput(n: int, teams: seq<(int, int)>)
{
  n >= 2 && |teams| == n &&
  (forall i :: 0 <= i < n ==> teams[i].0 != teams[i].1) &&
  (forall i :: 0 <= i < n ==> |set j | 0 <= j < n && teams[j].0 == teams[i].1| <= n - 1)
}

predicate ValidOutput(n: int, teams: seq<(int, int)>, result: seq<(int, int)>)
  requires |teams| == n
{
  |result| == n &&
  (forall i :: 0 <= i < n ==> result[i].0 + result[i].1 == 2 * (n - 1)) &&
  (forall i :: 0 <= i < n ==> result[i].0 >= n - 1) &&
  (forall i :: 0 <= i < n ==> result[i].1 >= 0) &&
  (forall i :: 0 <= i < n ==> 
    var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[i].1|;
    result[i].0 == (n - 1) + homeCount &&
    result[i].1 == (n - 1) - homeCount)
}

// <vc-helpers>
lemma HomeCountBounds(n: int, teams: seq<(int, int)>, i: int)
  requires n >= 2
  requires |teams| == n
  requires 0 <= i < n
  requires forall k :: 0 <= k < n ==> teams[k].0 != teams[k].1
  requires forall k :: 0 <= k < n ==> |set j | 0 <= j < n && teams[j].0 == teams[k].1| <= n - 1
  ensures var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[i].1|;
          0 <= homeCount <= n - 1
{
  var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[i].1|;
  var homeSet := set j | 0 <= j < n && teams[j].0 == teams[i].1;
  
  assert homeSet <= set j {:trigger} | 0 <= j < n;
  assert |set j {:trigger} | 0 <= j < n| == n;
  assert homeCount <= n;
  
  if teams[i].1 in set j | 0 <= j < n && teams[j].0 == teams[i].1 {
    var witnessJ :| 0 <= witnessJ < n && teams[witnessJ].0 == teams[i].1;
    assert teams[witnessJ].0 != teams[witnessJ].1;
    assert teams[i].1 != teams[witnessJ].1;
  }
}

lemma SetCardinalityLemma(n: int)
  requires n >= 0
  ensures |set j | 0 <= j < n| == n
{
  if n == 0 {
    assert set j | 0 <= j < n == {};
  } else {
    var s := set j | 0 <= j < n;
    assert s == set k | 0 <= k < n;
    SetCardinalityHelper(n, 0);
  }
}

lemma SetCardinalityHelper(n: int, start: int)
  requires 0 <= start <= n
  ensures |set j | start <= j < n| == n - start
{
  if start == n {
    assert set j | start <= j < n == {};
  } else {
    var s1 := set j | start <= j < n;
    var s2 := set j | start + 1 <= j < n;
    assert s1 == {start} + s2;
    assert start !in s2;
    SetCardinalityHelper(n, start + 1);
    assert |s1| == 1 + |s2|;
  }
}

lemma ResultProperties(n: int, teams: seq<(int, int)>, i: int, homeCount: int)
  requires n >= 2
  requires |teams| == n
  requires 0 <= i < n
  requires homeCount == |set j | 0 <= j < n && teams[j].0 == teams[i].1|
  requires 0 <= homeCount <= n - 1
  ensures (n - 1) + homeCount + ((n - 1) - homeCount) == 2 * (n - 1)
  ensures (n - 1) + homeCount >= n - 1
  ensures (n - 1) - homeCount >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, teams: seq<(int, int)>) returns (result: seq<(int, int)>)
  requires ValidInput(n, teams)
  ensures ValidOutput(n, teams, result)
// </vc-spec>
// <vc-code>
{
  result := [];
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> 
      var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[k].1|;
      result[k].0 == (n - 1) + homeCount &&
      result[k].1 == (n - 1) - homeCount
    invariant forall k :: 0 <= k < i ==> result[k].0 + result[k].1 == 2 * (n - 1)
    invariant forall k :: 0 <= k < i ==> result[k].0 >= n - 1
    invariant forall k :: 0 <= k < i ==> result[k].1 >= 0
  {
    var homeCount := |set j | 0 <= j < n && teams[j].0 == teams[i].1|;
    
    SetCardinalityLemma(n);
    HomeCountBounds(n, teams, i);
    ResultProperties(n, teams, i, homeCount);
    
    var points := ((n - 1) + homeCount, (n - 1) - homeCount);
    result := result + [points];
    
    i := i + 1;
  }
}
// </vc-code>

