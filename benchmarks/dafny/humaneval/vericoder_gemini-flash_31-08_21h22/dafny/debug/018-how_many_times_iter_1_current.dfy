

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
  while i <= |s| - |substr|
    invariant 0 <= i <= |s| - |substr| + 1
    invariant count == |set k {:trigger} | 0 <= k < i && s[k..k+|substr|] == substr|
  {
    if |substr| == 0 then
      // Handle the case where substr is empty. Every position matches.
      // If s is empty, i would be 0, |s| is 0, |substr| is 0. 0 <= 0-0 is true.
      // If s is "a", |s|=1, |substr|=0. i=0, 0 <= 1-0. Match. i=1, 1 <= 1-0. Match.
      // The postcondition for an empty substr is |s|+1.
      // (This loop counts up to |s| then increments count for s[|s|])
      // However, the provided postcondition `s[i..i+|substr|] == substr` explicitly
      // triggers on `s[i..i+|substr|]`. If `|substr| == 0`, `s[i..i]` is always `""`.
      // The set comprehension counts indices `i` where `s[i..i]` (which is `""`) equals `""`.
      // This happens for every `i` from `0` to `|s|`.
      // So the expected count is `|s| + 1`.

      // The loop condition `i <= |s| - |substr|` handles `|substr| == 0` as `i <= |s|`.
      // So `i` goes from `0` to `|s|`. Each iteration increments `count`.
      // This correctly yields `|s|+1` for `|substr| == 0`.
      if s[i..i+|substr|] == substr then
        count := count + 1;
      i := i + 1;
    else if i + |substr| <= |s| && s[i..i+|substr|] == substr then
      count := count + 1;
      i := i + 1;
    else
      i := i + 1;
  }
  return count;
}
// </vc-code>

