

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
  var i := 0;
  while i <= max
    invariant 0 <= i <= max + 1
    invariant times == |set j {:trigger} | 0 <= j < i && s[j..j+|substr|] == substr|
  {
    if s[i..i+|substr|] == substr {
      times := times + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

