predicate IsStrongestInSchool(student_idx: int, powers: seq<int>, schools: seq<int>)
  requires 0 <= student_idx < |powers| && |powers| == |schools|
{
  forall j :: 0 <= j < |powers| && schools[j] == schools[student_idx] ==> powers[j] <= powers[student_idx]
}

// <vc-helpers>
predicate IsStrongestInSchool(student_idx: int, powers: seq<int>, schools: seq<int>)
  requires 0 <= student_idx < |powers| && |powers| == |schools|
{
  forall j {:trigger schools[j]} :: 0 <= j < |powers| && schools[j] == schools[student_idx] ==> powers[j] <= powers[student_idx]
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
  ghost var relevant_set: set<int> := {};
  var count := 0;
  for i: int := 0 to k-1
    invariant 0 <= i <= k
    invariant |relevant_set| == count
    invariant count >= 0
    invariant count <= k
    invariant relevant_set == (set j: int | 0 <= j < i && !IsStrongestInSchool(chosen[j]-1, powers, schools))
  {
    if !IsStrongestInSchool(chosen[i]-1, powers, schools) {
      relevant_set := relevant_set + {i};
      count := count + 1;
    }
  }
  assert relevant_set == (set i: int | 0 <= i < k && !IsStrongestInSchool(chosen[i]-1, powers, schools));
  return count;
}
// </vc-code>

