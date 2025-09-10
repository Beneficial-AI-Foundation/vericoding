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
// No additional helpers needed; existing predicates are sufficient.
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
    invariant forall k1, k2 :: 0 <= k1 < k2 < i ==> words[k1] != words[k2]
  {
    if words[i] in seen || exists k :: 0 <= k < i && words[k] == words[i] {
      isValid := false;
    } else {
      seen := seen + {words[i]};
    }
    i := i + 1;
  }
  // Check ConsecutiveCharsMatch
  var j := 0;
  while j < |words| - 1
    invariant 0 <= j <= |words| - 1
  {
    if words[j][|words[j]| - 1] != words[j+1][0] {
      isValid := false;
    }
    j := j + 1;
  }
  // Set result based on validity
  var result := if isValid then "Yes" else "No";
  return result;
}
// </vc-code>

