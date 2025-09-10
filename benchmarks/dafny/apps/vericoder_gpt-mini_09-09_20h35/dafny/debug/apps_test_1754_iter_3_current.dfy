predicate IsStrongestInSchool(student_idx: int, powers: seq<int>, schools: seq<int>)
  requires 0 <= student_idx < |powers| && |powers| == |schools|
{
  forall j :: 0 <= j < |powers| && schools[j] == schools[student_idx] ==> powers[j] <= powers[student_idx]
}

// <vc-helpers>
function CountNotStrong(i: int, chosen: seq<int>, powers: seq<int>, schools: seq<int>): int
  requires 0 <= i <= |chosen|
  requires |powers| == |schools|
  requires forall j :: 0 <= j < |chosen| ==> 1 <= chosen[j] <= |powers|
  decreases i
{
  if i == 0 then 0 else CountNotStrong(i-1, chosen, powers, schools) + (if !IsStrongestInSchool(chosen[i-1]-1, powers, schools) then 1 else 0)
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
  var i := 0;
  var cnt := 0;
  while i < k
    invariant 0 <= i <= k
    invariant 0 <= cnt <= i
    invariant cnt == CountNotStrong(i, chosen, powers, schools)
  {
    var idx := chosen[i] - 1;
    if !IsStrongestInSchool(idx, powers, schools) {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  result := cnt;
}
// </vc-code>

