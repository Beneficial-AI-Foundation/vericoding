// <vc-preamble>
predicate ValidInput(s: string)
{
    |s| >= 0 && forall i :: 0 <= i < |s| ==> s[i] in {'A', 'B', 'C', '.'}
}

predicate HasAllThreeColors(s: string, start: int)
    requires 0 <= start <= |s| - 3
{
    'A' in s[start..start+3] && 'B' in s[start..start+3] && 'C' in s[start..start+3]
}

predicate PossibleToGetAllColors(s: string)
{
    |s| >= 3 && exists i :: 0 <= i <= |s| - 3 && HasAllThreeColors(s, i)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Predicate HasAllThreeColorsAtIndex rewritten using set to check for all three colors, fixing the syntax error where `if` statements in Dafny predicates require `then` and `else` blocks explicitly or combined with boolean expressions. The original approach with `var` was also not idiomatic for predicates, which should ideally be purely functional. */
predicate HasAllThreeColorsAtIndex(s: string, start: int)
    requires 0 <= start <= |s| - 3
{
    var sub := s[start..start+3];
    'A' in sub && 'B' in sub && 'C' in sub
}

lemma HasAllThreeColorsEquivalent(s: string, start: int)
    requires 0 <= start <= |s| - 3
    ensures HasAllThreeColors(s, start) <==> HasAllThreeColorsAtIndex(s, start)
{
    // The two predicates are definitionally equivalent. The lemma body can be empty.
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == "Yes" ==> PossibleToGetAllColors(s)
    ensures result == "No" ==> !PossibleToGetAllColors(s)
    ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): No changes needed in this section as the previous fix was to the helper. */
{
  if |s| < 3 {
    return "No";
  }

  var found := false;
  var i := 0;
  while i <= |s| - 3
    invariant 0 <= i <= |s| - 2
    invariant !found ==> forall j :: 0 <= j < i ==> !HasAllThreeColors(s, j)
  {
    if HasAllThreeColors(s, i) {
      found := true;
      break;
    }
    i := i + 1;
  }

  if found {
    return "Yes";
  } else {
    return "No";
  }
}
// </vc-code>
