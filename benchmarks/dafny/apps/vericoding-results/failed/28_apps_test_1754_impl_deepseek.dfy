predicate IsStrongestInSchool(student_idx: int, powers: seq<int>, schools: seq<int>)
  requires 0 <= student_idx < |powers| && |powers| == |schools|
{
  forall j :: 0 <= j < |powers| && schools[j] == schools[student_idx] ==> powers[j] <= powers[student_idx]
}

// <vc-helpers>
predicate IsStrongestInSchool(student_idx: int, powers: seq<int>, schools: seq<int>)
  requires 0 <= student_idx < |powers| && |powers| == |schools|
{
  forall j :: 0 <= j < |powers| && schools[j] == schools[student_idx] ==> powers[j] <= powers[student_idx]
}

lemma lemma_strongest_exists(s: int, powers: seq<int>, schools: seq<int>)
  requires |powers| == |schools|
  requires forall i :: 0 <= i < |powers| ==> 1 <= schools[i]
  requires exists i :: 0 <= i < |powers| && schools[i] == s
  ensures exists j :: 0 <= j < |powers| && schools[j] == s && IsStrongestInSchool(j, powers, schools)
{
  var i :| 0 <= i < |powers| && schools[i] == s;
  var max_power := powers[i];
  var max_idx := i;
  var idx := 0;
  while idx < |powers|
    invariant 0 <= idx <= |powers|
    invariant max_idx >= 0 && max_idx < |powers|
    invariant schools[max_idx] == s
    invariant max_power == powers[max_idx]
    invariant forall j :: 0 <= j < idx && schools[j] == s ==> powers[j] <= max_power
  {
    if schools[idx] == s && powers[idx] > max_power {
      max_power := powers[idx];
      max_idx := idx;
    }
    idx := idx + 1;
  }
  assert IsStrongestInSchool(max_idx, powers, schools);
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
    invariant count == |set j | 0 <= j < i && !IsStrongestInSchool(chosen[j]-1, powers, schools)|
  {
    var student_idx := chosen[i] - 1;
    assert 0 <= student_idx < n;  // Since chosen[i] between 1 and n
    if !IsStrongestInSchool(student_idx, powers, schools) {
      count := count + 1;
    }
    i := i + 1;
  }
  result := count;
}
// </vc-code>

