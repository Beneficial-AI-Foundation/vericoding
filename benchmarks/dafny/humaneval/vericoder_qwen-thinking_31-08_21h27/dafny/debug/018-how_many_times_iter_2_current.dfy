

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
  var L := |substr|;
  var n := |s|;
  if L == 0 {
    times := n + 1;
  } else {
    times := 0;
    var i := 0;
    while i <= n - L
      invariant 0 <= i <= n - L + 1
      invariant times == |{ j : int | 0 <= j < i && s[j..j+L] == substr }|
    {
      if s[i..i+L] == substr {
        times := times + 1;
      }
      i := i + 1;
    }
  }
}
// </vc-code>

