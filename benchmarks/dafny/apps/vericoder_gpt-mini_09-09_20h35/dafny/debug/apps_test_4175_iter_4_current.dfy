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
lemma MismatchImpliesNotConsec(words: seq<string>, idx: int)
  requires 0 <= idx < |words| - 1
  requires words[idx][|words[idx]| - 1] != words[idx+1][0]
  ensures !ConsecutiveCharsMatch(words)
{
  // Use idx as a witness for the existential that negates the universal in ConsecutiveCharsMatch
  assert 0 <= idx < |words| - 1;
  assert words[idx][|words[idx]| - 1] != words[idx+1][0];
  var k := idx;
  assert 0 <= k < |words| - 1;
  assert words[k][|words[k]| - 1] != words[k+1][0];
  assert exists m :: 0 <= m < |words| - 1 && words[m][|words[m]| - 1] != words[m+1][0];
}

lemma RepeatImpliesNotNoRepeats(words: seq<string>, i: int)
  requires 0 <= i < |words|
  requires exists j :: 0 <= j < i && words[j] == words[i]
  ensures !NoRepeats(words)
{
  // Extract a witness j that repeats words[i]
  var j :| 0 <= j < i && words[j] == words[i];
  assert 0 <= j < i < |words|;
  assert words[j] == words[i];
  // Use j and i as witnesses for the existential that negates the universal in NoRepeats
  assert exists p, q :: 0 <= p < q < |words| && words[p] == words[q];
}

lemma SeenContainsWitness(seen: set<string>, words: seq<string>, i: int, x: string)
  requires seen == set k | 0 <= k < i :: words[k]
  requires x in seen
  ensures exists j :: 0 <= j < i && words[j] == x
{
  var j :| 0 <= j < i && words[j] == x;
}
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
    invariant seen == set k | 0 <= k < i :: words[k]
    invariant forall p, q :: 0 <= p < q < i ==> words[p] != words[q]
    invariant forall k :: 0 <= k < i-1 ==> words[k][|words[k]| - 1] == words[k+1][0]
  {
    if i > 0 {
      if words[i-1][|words[i-1]| - 1] != words[i][0] {
        // prove that the shiritori condition fails
        MismatchImpliesNotConsec(words, i-1);
        assert !ValidShiritori(words);
        result := "No";
        return;
      }
    }
    if words[i] in seen {
      // From seen == set k | 0 <= k < i :: words[k], derive the witness
      SeenContainsWitness(seen, words, i, words[i]);
      RepeatImpliesNotNoRepeats(words, i);
      assert !ValidShiritori(words);
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

