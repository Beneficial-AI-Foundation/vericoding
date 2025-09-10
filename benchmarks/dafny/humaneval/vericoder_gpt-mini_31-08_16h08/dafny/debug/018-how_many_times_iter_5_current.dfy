

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method how_many_times(s: string, substr: string) returns (times: int)
    // post-condition-start
    ensures times == |set i {:trigger} | 0 <= i <= |s| - |substr| && s[i..i+|substr|] == substr|
    // post-condition-end
// </vc-spec>
// <vc-code>
{
  if |substr| > |s| {
    times := 0;
    return;
  }
  var max := |s| - |substr|;
  times := 0;
  ghost var seen: set<int> := {};
  var i := 0;
  while i <= max
    invariant 0 <= i <= max + 1
    invariant times == |seen|
    invariant seen == set j | 0 <= j < i && s[j..j+|substr|] == substr :: j
  {
    if s[i..i+|substr|] == substr {
      ghost { seen := seen + {i}; }
      times := times + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

