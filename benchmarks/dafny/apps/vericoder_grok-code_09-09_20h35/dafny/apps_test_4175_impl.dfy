predicate NoRepeats(words: seq<string>)
{
    forall i, j :: 0 <= i < j < |words| ==> words[i] != words[j]
}

predicate ConsecutiveCharsMatch(words: seq<string>)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
{
    forall i :: 0 <= i < |words| - 1 ==> words[i][|words[i]| - 1] == words[i+1][0]
}

predicate ValidShiritori(words: seq<string>)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
{
    NoRepeats(words) && ConsecutiveCharsMatch(words)
}

// <vc-helpers>
//No additional helpers, but to support the proofs, we ensure the invariants are strengthened.
//We add the invariant 'isValid ==> |seen| == i' and '|seen| <= i' in the code.
//Additionally, we add assertions after the loops to verify the predicates.
// </vc-helpers>

// <vc-spec>
method solve(words: seq<string>) returns (result: string)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> ValidShiritori(words)
// </vc-spec>
// <vc-code>
{
  var isValid := true;
  // Check NoRepeats using a set
  var seen: set<string> := {};
  var i := 0;
  while i < |words|
    invariant 0 <= i <= |words|
    invariant forall k :: 0 <= k < i ==> words[k] in seen
    invariant |seen| <= i
    invariant isValid ==> |seen| == i
    invariant isValid ==> forall k1, k2 :: 0 <= k1 < k2 < i ==> words[k1] != words[k2]
  {
    if words[i] in seen {
      isValid := false;
    } else {
      seen := seen + {words[i]};
    }
    i := i + 1;
  }
  if isValid {
    assert NoRepeats(words);
  }
  // Check ConsecutiveCharsMatch
  var j := 0;
  while j + 1 < |words|
    invariant 0 <= j <= |words|
    invariant isValid ==> forall p :: 0 <= p < j ==> words[p][|words[p]| - 1] == words[p+1][0]
  {
    if words[j][|words[j]| - 1] != words[j+1][0] {
      isValid := false;
    }
    j := j + 1;
  }
  if isValid {
    assert ConsecutiveCharsMatch(words);
  }
  // Set result based on validity
  result := if isValid then "Yes" else "No";
  return result;
}
// </vc-code>

