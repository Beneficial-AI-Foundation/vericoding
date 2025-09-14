

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
// </vc-spec>
// <vc-code>
{
  if |sub| > |main| then {
    return false;
  }
  
  if |sub| == 0 then {
    return true;
  }

  var i := 0;
  while i <= |main| - |sub|
    invariant 0 <= i <= |main| - |sub|
    // The previous decreases clause was incorrect, should be based on a non-negative expression that decreases towards zero.
    // (main - sub) - i can be rephrased as (|main| - |sub|) - i.
    // The loop terminates when i > |main| - |sub|. The distance decreases with each iteration.
    decreases (|main| - |sub|) - i
  {
    if main[i..i + |sub|] == sub then {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

