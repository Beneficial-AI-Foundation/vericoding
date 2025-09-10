predicate IsStrongestInSchool(student_idx: int, powers: seq<int>, schools: seq<int>)
  requires 0 <= student_idx < |powers| && |powers| == |schools|
{
  forall j :: 0 <= j < |powers| && schools[j] == schools[student_idx] ==> powers[j] <= powers[student_idx]
}

// <vc-helpers>
lemma SetComprehensionSize(k: int, chosen: seq<int>, powers: seq<int>, schools: seq<int>)
  requires k >= 0 && |chosen| == k
  requires |powers| == |schools|
  requires forall i :: 0 <= i < k ==> 1 <= chosen[i] <= |powers|
  ensures |set i | 0 <= i < k && !IsStrongestInSchool(chosen[i]-1, powers, schools)| <= k
{
  var s := set i | 0 <= i < k && !IsStrongestInSchool(chosen[i]-1, powers, schools);
  assert s <= set i | 0 <= i < k;
  assert |set i | 0 <= i < k| <= k;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int, powers: seq<int>, schools: seq<int>, chosen: seq<int>) returns (result: int)
  requires n >= 1 && m >= 1 && k >= 1 && k <= n && m <= n
  requires |powers| == n && |schools| == n && |chosen| == k
  requires forall i :: 0 <= i < n ==> 1 <= schools[i] <= m
  requires forall i :: 0 <= i < k ==> 1 <= chosen[i] <= n
  requires forall i, j :: 0 <= i < k && 0 <= j < k && i != j ==> chosen[i] != chosen[j]
  requires forall i, j :: 0 <= i < n && 0 <= j < n && i != j ==> powers[i] != powers[j]
  requires forall s :: 1 <= s <= m ==> exists i :: 0 <= i < n && schools[i] == s
  requires forall i :: 0 <= i < n ==> 1 <= powers[i] <= n
  ensures result >= 0 && result <= k
  ensures result == |set i | 0 <= i < k && !IsStrongestInSchool(chosen[i]-1, powers, schools)|
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var processed := {};
  
  for idx := 0 to k
    invariant 0 <= idx <= k
    invariant processed == set i | 0 <= i < idx && !IsStrongestInSchool(chosen[i]-1, powers, schools)
    invariant count == |processed|
    invariant count <= idx
  {
    var student_idx := chosen[idx] - 1;
    
    // Check if this student is the strongest in their school
    var isStrongest := true;
    var school := schools[student_idx];
    var power := powers[student_idx];
    
    for j := 0 to n
      invariant 0 <= j <= n
      invariant isStrongest <==> (forall jj :: 0 <= jj < j && schools[jj] == school ==> powers[jj] <= power)
    {
      if schools[j] == school && powers[j] > power {
        isStrongest := false;
      }
    }
    
    if !isStrongest {
      processed := processed + {idx};
      count := count + 1;
    }
    
    assert processed == set i | 0 <= i < idx + 1 && !IsStrongestInSchool(chosen[i]-1, powers, schools);
  }
  
  assert processed == set i | 0 <= i < k && !IsStrongestInSchool(chosen[i]-1, powers, schools);
  result := count;
}
// </vc-code>

