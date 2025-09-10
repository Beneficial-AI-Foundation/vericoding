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

// </vc-helpers>

// <vc-spec>
method solve(words: seq<string>) returns (result: string)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> ValidShiritori(words)
// </vc-spec>
// <vc-code>
{
  var seen: set<string> := {};
  var i := 0;
  while i < |words|
    invariant 0 <= i <= |words|
    invariant forall k :: 0 <= k < i ==> words[k] in seen
    invariant forall p, q :: 0 <= p < q < i ==> words[p] != words[q]
    invariant forall k :: 0 <= k < i-1 ==> words[k][|words[k]| - 1] == words[k+1][0]
  {
    if i > 0 {
      if words[i-1][|words[i-1]| - 1] != words[i][0] {
        result := "No";
        return;
      }
    }
    if words[i] in seen {
      result := "No";
      return;
    }
    seen := seen + {words[i]};
    i := i + 1;
  }
  result := "Yes";
  return;
}
// </vc-code>

