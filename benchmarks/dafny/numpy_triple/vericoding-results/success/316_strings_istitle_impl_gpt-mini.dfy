// <vc-preamble>
// Helper predicates for character classification
predicate IsUpper(c: char)
{
    'A' <= c <= 'Z'
}

predicate IsLower(c: char)
{
    'a' <= c <= 'z'
}

predicate IsAlpha(c: char)
{
    IsUpper(c) || IsLower(c)
}

predicate IsCased(c: char)
{
    IsUpper(c) || IsLower(c)
}

// Helper predicate to check if sequence contains at least one cased character
predicate HasCasedChar(chars: seq<char>)
{
    exists i :: 0 <= i < |chars| && IsCased(chars[i])
}

// Recursive helper to check titlecase pattern
predicate CheckTitleCase(chars: seq<char>, expectUpper: bool)
    decreases |chars|
{
    if |chars| == 0 then
        true
    else
        var c := chars[0];
        var rest := chars[1..];
        if IsUpper(c) then
            expectUpper && CheckTitleCase(rest, false)
        else if IsLower(c) then
            !expectUpper && CheckTitleCase(rest, false)
        else
            // Non-alphabetic character - next alphabetic char should be uppercase
            CheckTitleCase(rest, true)
}

// Main predicate to determine if a string is titlecased
predicate IsTitlecased(s: string)
{
    |s| > 0 &&
    HasCasedChar(s) &&
    CheckTitleCase(s, true)
}

// Main method implementing numpy.strings.istitle
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): implemented TitlecasedBool as direct function returning IsTitlecased */
function TitlecasedBool(s: string): bool {
    IsTitlecased(s)
}
// </vc-helpers>

// <vc-spec>
method istitle(a: seq<string>) returns (result: seq<bool>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == IsTitlecased(a[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate over input and compute titlecase booleans */
  var res: seq<bool> := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant forall j :: 0 <= j < |res| ==> res[j] == IsTitlecased(a[j])
  {
    var b := TitlecasedBool(a[i]);
    res := res + [b];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
