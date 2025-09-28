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
/* helper modified by LLM (iteration 2): FirstIndex function returning leftmost index */
function FirstIndex(s: string, sub: string, start: int, endPos: int): int
  requires 0 <= start && start <= endPos && endPos <= |s|
  requires SubstringExistsInRange(s, sub, start, endPos)
  decreases endPos - start
{
  if SubstringAt(s, sub, start as nat) then start else FirstIndex(s, sub, start + 1, endPos)
}

/* helper modified by LLM (iteration 2): Lemma proving properties of FirstIndex */
lemma FirstIndexProperties(s: string, sub: string, start: int, endPos: int)
  requires 0 <= start && start <= endPos && endPos <= |s|
  requires SubstringExistsInRange(s, sub, start, endPos)
  ensures start <= FirstIndex(s, sub, start, endPos) <= endPos
  ensures FirstIndex(s, sub, start, endPos) as nat + |sub| <= |s|
  ensures SubstringAt(s, sub, FirstIndex(s, sub, start, endPos) as nat)
  ensures forall j: nat :: start <= j as int < FirstIndex(s, sub, start, endPos) ==> !SubstringAt(s, sub, j)
  decreases endPos - start
{
  if SubstringAt(s, sub, start as nat) {
    assert FirstIndex(s, sub, start, endPos) == start;
    // immediate consequences
    assert start <= endPos;
    assert SubstringAt(s, sub, start as nat);
    assert start as nat + |sub| <= |s|;
  } else {
    // substring does not match at `start`, so it must exist later by precondition
    FirstIndexProperties(s, sub, start + 1, endPos);
    assert FirstIndex(s, sub, start, endPos) == FirstIndex(s, sub, start + 1, endPos);
    // bounds and properties follow from the recursive call
  }
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
  /* code modified by LLM (iteration 2): iterate over inputs and compute first indices using helper */
  var n := |a|;
  var res := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> (
      res[k] >= 0 &&
      start[k] <= res[k] <= endPos[k] &&
      res[k] as nat + |sub[k]| <= |a[k]| &&
      SubstringAt(a[k], sub[k], res[k] as nat) &&
      (forall j: nat :: start[k] <= j as int < res[k] ==> !SubstringAt(a[k], sub[k], j))
    )
    decreases n - i
  {
    res[i] := FirstIndex(a[i], sub[i], start[i], endPos[i]);
    FirstIndexProperties(a[i], sub[i], start[i], endPos[i]);
    i := i + 1;
  }
  result := res[..];
}

// </vc-code>
