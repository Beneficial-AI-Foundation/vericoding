predicate IsStrongestInSchool(student_idx: int, powers: seq<int>, schools: seq<int>)
  requires 0 <= student_idx < |powers| && |powers| == |schools|
{
  forall j :: 0 <= j < |powers| && schools[j] == schools[student_idx] ==> powers[j] <= powers[student_idx]
}

// <vc-helpers>
lemma IsStrongestHelperLemma(student_idx: int, powers: seq<int>, schools: seq<int>)
  requires 0 <= student_idx < |powers| && |powers| == |schools|
  ensures IsStrongestInSchool(student_idx, powers, schools) <==> 
    forall j :: 0 <= j < |powers| && schools[j] == schools[student_idx] ==> powers[j] <= powers[student_idx]
{
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
  var weak_students: set<int> := {};
  
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant count == |weak_students|
    invariant weak_students == set j | 0 <= j < i && !IsStrongestInSchool(chosen[j]-1, powers, schools)
    invariant count <= i
  {
    var student_idx := chosen[i] - 1;
    
    var is_strongest := true;
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant is_strongest ==> forall l :: 0 <= l < j && schools[l] == schools[student_idx] ==> powers[l] <= powers[student_idx]
      invariant !is_strongest ==> exists l :: 0 <= l < j && schools[l] == schools[student_idx] && powers[l] > powers[student_idx]
    {
      if schools[j] == schools[student_idx] && powers[j] > powers[student_idx] {
        is_strongest := false;
      }
      j := j + 1;
    }
    
    assert is_strongest <==> IsStrongestInSchool(student_idx, powers, schools);
    
    if !is_strongest {
      weak_students := weak_students + {i};
      count := count + 1;
    }
    
    i := i + 1;
  }
  
  result := count;
}
// </vc-code>

