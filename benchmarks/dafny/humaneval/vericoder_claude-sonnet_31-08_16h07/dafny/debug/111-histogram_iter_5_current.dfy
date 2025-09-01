type BiggestMap = map<int, int>

// <vc-helpers>
function count_occurrences(a: seq<int>, val: int): int
{
  |set j | 0 <= j < |a| && a[j] == val|
}

function max_count(a: seq<int>): int
  requires |a| > 0
{
  if |a| == 1 then 1
  else
    var first_count := count_occurrences(a, a[0]);
    var rest_max := max_count(a[1..]);
    var rest_first_count := count_occurrences(a[1..], a[0]);
    var adjusted_first := if rest_first_count > 0 then first_count else 1;
    if adjusted_first >= rest_max then adjusted_first else rest_max
}

lemma count_occurrences_positive(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures count_occurrences(a, a[i]) > 0
{
  assert i in set j | 0 <= j < |a| && a[j] == a[i];
}

lemma max_count_properties(a: seq<int>)
  requires |a| > 0
  ensures max_count(a) > 0
  ensures forall i :: 0 <= i < |a| ==> count_occurrences(a, a[i]) <= max_count(a)
  ensures exists i :: 0 <= i < |a| && count_occurrences(a, a[i]) == max_count(a)
{
  if |a| == 1 {
    count_occurrences_positive(a, 0);
  } else {
    max_count_properties(a[1..]);
    count_occurrences_positive(a, 0);
    
    forall i | 0 <= i < |a| 
      ensures count_occurrences(a, a[i]) <= max_count(a)
    {
      if i == 0 {
        // Proved by definition of max_count
      } else {
        assert a[i] == a[1..][i-1];
        assert count_occurrences(a, a[i]) <= count_occurrences(a[1..], a[i]) + 1;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>) returns (biggest: BiggestMap)
  // post-conditions-start
  ensures forall i :: 0 <= i < |a| && a[i] in biggest ==>
    biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest ==>
    biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest ==>
    biggest[a[i]] == biggest[a[j]]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |a| == 0 {
    biggest := map[];
    return;
  }
  
  max_count_properties(a);
  var max_cnt := max_count(a);
  
  var result: BiggestMap := map[];
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall val :: val in result ==> count_occurrences(a, val) == max_cnt
    invariant forall val :: val in result ==> result[val] == max_cnt
    invariant forall j :: 0 <= j < i && count_occurrences(a, a[j]) == max_cnt ==> a[j] in result
  {
    var cnt := count_occurrences(a, a[i]);
    if cnt == max_cnt {
      result := result[a[i] := cnt];
    }
    i := i + 1;
  }
  
  biggest := result;
}
// </vc-code>

