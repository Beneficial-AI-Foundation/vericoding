predicate IsStrongestInSchool(student_idx: int, powers: seq<int>, schools: seq<int>)
  requires 0 <= student_idx < |powers| && |powers| == |schools|
{
  forall j :: 0 <= j < |powers| && schools[j] == schools[student_idx] ==> powers[j] <= powers[student_idx]
}

// <vc-helpers>
lemma SetComprehensionSize(k: int)
  requires k >= 0
  ensures |set i {:trigger i in (set i | 0 <= i < k)} | 0 <= i < k| <= k
{
  if k == 0 {
    assert (set i {:trigger i in (set i | 0 <= i < 0)} | 0 <= i < 0) == {};
  } else {
    SetComprehensionSize(k - 1);
    var s1 := set i {:trigger i in s1} | 0 <= i < k - 1;
    var s2 := set i {:trigger i in s2} | 0 <= i < k;
    
    if k - 1 in s1 {
      assert s2 == s1;
    } else {
      assert s2 == s1 + {k - 1};
      assert |s2| <= |s1| + 1;
    }
  }
}

lemma SubsetSize<T>(s1: set<T>, s2: set<T>)
  requires s1 <= s2
  ensures |s1| <= |s2|
{
  if s1 == s2 {
    assert |s1| == |s2|;
  } else {
    var elem :| elem in s2 && elem !in s1;
    var s2' := s2 - {elem};
    assert s1 <= s2';
    if s1 == s2' {
      assert |s2| == |s2'| + 1;
      assert |s1| == |s2'|;
      assert |s1| < |s2|;
    } else {
      SubsetSize(s1, s2');
      assert |s1| <= |s2'|;
      assert |s2| == |s2'| + 1;
      assert |s1| <= |s2|;
    }
  }
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
  var notStrongestSet: set<int> := {};
  
  for idx := 0 to k
    invariant 0 <= idx <= k
    invariant notStrongestSet == set i {:trigger i in notStrongestSet} | 0 <= i < idx && !IsStrongestInSchool(chosen[i]-1, powers, schools)
    invariant count == |notStrongestSet|
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
    
    var oldSet := notStrongestSet;
    if !isStrongest {
      notStrongestSet := notStrongestSet + {idx};
      count := count + 1;
    }
    
    assert notStrongestSet == set i {:trigger i in notStrongestSet} | 0 <= i < idx + 1 && !IsStrongestInSchool(chosen[i]-1, powers, schools);
  }
  
  var finalSet := set i {:trigger i in finalSet} | 0 <= i < k && !IsStrongestInSchool(chosen[i]-1, powers, schools);
  assert finalSet == notStrongestSet;
  assert finalSet <= set i {:trigger i in finalSet} | 0 <= i < k;
  SetComprehensionSize(k);
  SubsetSize(finalSet, set i {:trigger i in finalSet} | 0 <= i < k);
  assert |finalSet| <= k;
  
  result := count;
}
// </vc-code>

