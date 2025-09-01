

// <vc-helpers>

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
  if |s| - |substr| < -1 {
    times := 0;
  } else {
    while i <= |s| - |substr|
      invariant 0 <= i <= |s| - |substr| + 1
      invariant count == |set j | 0 <= j < i && s[j..j+|substr|] == substr|
    {
      if s[i..i+|substr|] == substr {
        count := count + 1;
      }
      i := i + 1;
    }
    times := count;
  }
}
// </vc-code>

