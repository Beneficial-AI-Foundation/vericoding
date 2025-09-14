

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures true <== (exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|])
// </vc-spec>
// <vc-code>
{
  if |sub| > |main| {
    return false;
  }
  return exists i :: 0 <= i <= |main| - |sub| && sub == main[i..i + |sub|];
}
// </vc-code>

