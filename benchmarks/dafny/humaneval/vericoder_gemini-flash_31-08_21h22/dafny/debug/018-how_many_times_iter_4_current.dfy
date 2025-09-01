

// <vc-helpers>
predicate {:opaque} Matches(s: string, start: int, substr: string)
  requires 0 <= start
  requires 0 <= |substr|
{
  start + |substr| <= |s| && s[start .. start + |substr|] == substr
}
// </vc-helpers>

// <vc-spec>
method how_many_times(s: string, substr: string) returns (times: int)
    // post-condition-start
    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
    // post-condition-end
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var i := 0;
  while i <= |s| - |substr|
    invariant 0 <= i <= |s| - |substr| + 1
    invariant |substr| == 0 ==> count == i
    invariant |substr| != 0 ==> count == |set k {:trigger} | 0 <= k < i && Matches(s, k, substr)|
  {
    if |substr| == 0 {
      count := count + 1;
      i := i + 1;
    } else if Matches(s, i, substr) {
      count := count + 1;
      i := i + 1;
    } else {
      i := i + 1;
    }
  }
  return count;
}
// </vc-code>

