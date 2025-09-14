predicate IsStrongestInSchool(student_idx: int, powers: seq<int>, schools: seq<int>)
  requires 0 <= student_idx < |powers| && |powers| == |schools|
{
  forall j :: 0 <= j < |powers| && schools[j] == schools[student_idx] ==> powers[j] <= powers[student_idx]
}

// <vc-helpers>
lemma IsStrongestInSchoolImpliesUniqueInSchool(student_idx: int, powers: seq<int>, schools: seq<int>)
  requires 0 <= student_idx < |powers| && |powers| == |schools|
  requires IsStrongestInSchool(student_idx, powers, schools)
  requires forall i, j :: 0 <= i < |powers| && 0 <= j < |powers| && i != j ==> powers[i] != powers[j]
  ensures forall j :: 0 <= j < |powers| && schools[j] == schools[student_idx] && j != student_idx ==> powers[j] < powers[student_idx]
{
  forall j | 0 <= j < |powers| && schools[j] == schools[student_idx] && j != student_idx
  ensures powers[j] < powers[student_idx]
  {
    assert IsStrongestInSchool(student_idx, powers, schools);
    assert schools[j] == schools[student_idx];
    assert powers[j] <= powers[student_idx];
    if powers[j] == powers[student_idx] {
      assert powers[j] == powers[student_idx] && j != student_idx;
      assert false;
    }
  }
}

function countNonStrongest(chosen: seq<int>, powers: seq<int>, schools: seq<int>, i: int): int
  requires 0 <= i <= |chosen|
  ensures countNonStrongest(chosen, powers, schools, i) == |set j | 0 <= j < i && !IsStrongestInSchool(chosen[j]-1, powers, schools)|
{
  if i == 0 then 0 else
    countNonStrongest(chosen, powers, schools, i-1) + 
    (if !IsStrongestInSchool(chosen[i-1]-1, powers, schools) then 1 else 0)
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
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant count == countNonStrongest(chosen, powers, schools, i)
  {
    var student_index := chosen[i] - 1;
    if !IsStrongestInSchool(student_index, powers, schools) {
      count := count + 1;
    }
    i := i + 1;
  }
  result := count;
}
// </vc-code>

