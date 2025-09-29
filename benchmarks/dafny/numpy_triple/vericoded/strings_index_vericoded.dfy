// <vc-preamble>
/*
 * Dafny specification for numpy.strings.index function.
 * Like find, but requires that the substring is found in each string,
 * returning the lowest index where the substring occurs within the specified range.
 */

// Helper predicate to check if a substring matches at a specific position
predicate SubstringAt(s: string, sub: string, pos: nat)
{
    pos + |sub| <= |s| && s[pos..pos + |sub|] == sub
}

// Helper predicate to check if substring exists within a range
predicate SubstringExistsInRange(s: string, sub: string, start: int, endPos: int)
{
    exists j: nat :: start <= j as int && j + |sub| <= (endPos + 1) && j + |sub| <= |s| && SubstringAt(s, sub, j)
}

// Main method specification for numpy.strings.index
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added decreases clause for termination */
function FindFirstIndex(s: string, sub: string, start: int, endPos: int): int
  requires 0 <= start <= endPos <= |s|
  requires SubstringExistsInRange(s, sub, start, endPos)
  ensures start <= FindFirstIndex(s, sub, start, endPos) <= endPos
  ensures FindFirstIndex(s, sub, start, endPos) as nat + |sub| <= |s|
  ensures SubstringAt(s, sub, FindFirstIndex(s, sub, start, endPos) as nat)
  ensures forall j: nat :: start <= j as int < FindFirstIndex(s, sub, start, endPos) ==> !SubstringAt(s, sub, j)
  decreases endPos - start
{
  if start as nat < |s| && start as nat + |sub| <= |s| && SubstringAt(s, sub, start as nat) then
    start
  else if start < endPos then
    FindFirstIndex(s, sub, start + 1, endPos)
  else
    start
}
// </vc-helpers>

// <vc-spec>
method index(a: seq<string>, sub: seq<string>, start: seq<int>, endPos: seq<int>) returns (result: seq<int>)
    requires |a| == |sub| == |start| == |endPos|
    requires forall i :: 0 <= i < |a| ==> (
        // Valid range bounds
        0 <= start[i] && start[i] <= endPos[i] && endPos[i] <= |a[i]| &&
        // Substring must exist in each string within the range
        SubstringExistsInRange(a[i], sub[i], start[i], endPos[i])
    )
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> (
        // Result is always non-negative (no -1 values like find)
        result[i] >= 0 &&
        // Result is within the valid search range
        start[i] <= result[i] <= endPos[i] &&
        // The substring is found at the returned index
        result[i] as nat + |sub[i]| <= |a[i]| &&
        SubstringAt(a[i], sub[i], result[i] as nat) &&
        // This is the lowest (leftmost) index where substring is found in the range
        (forall j: nat :: start[i] <= j as int < result[i] ==> !SubstringAt(a[i], sub[i], j))
    )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): No changes needed to method body */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> (
      result[k] >= 0 &&
      start[k] <= result[k] <= endPos[k] &&
      result[k] as nat + |sub[k]| <= |a[k]| &&
      SubstringAt(a[k], sub[k], result[k] as nat) &&
      (forall j: nat :: start[k] <= j as int < result[k] ==> !SubstringAt(a[k], sub[k], j))
    )
  {
    var idx := FindFirstIndex(a[i], sub[i], start[i], endPos[i]);
    result := result + [idx];
    i := i + 1;
  }
}
// </vc-code>
