// <vc-preamble>
predicate IsStrongestInSchool(student_idx: int, powers: seq<int>, schools: seq<int>)
  requires 0 <= student_idx < |powers| && |powers| == |schools|
{
  forall j :: 0 <= j < |powers| && schools[j] == schools[student_idx] ==> powers[j] <= powers[student_idx]
}
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 5): Fixing loop invariant for count by moving it to the ensures clause and using a post-loop check for result. */
  var count := 0;
  for i := 0 to k - 1
    invariant 0 <= i <= k
    invariant 0 <= count
    invariant count == |set j | 0 <= j < i && !IsStrongestInSchool(chosen[j]-1, powers, schools)|
  {
    var student_idx := chosen[i] - 1;
    if !IsStrongestInSchool(student_idx, powers, schools) {
      count := count + 1;
    }
  }
  result := count;
  assert result == |set j | 0 <= j < k && !IsStrongestInSchool(chosen[j]-1, powers, schools)|;
}
// </vc-code>
