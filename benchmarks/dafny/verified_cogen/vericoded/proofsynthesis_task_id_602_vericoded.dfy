// <vc-preamble>
datatype Option<T> = None | Some(value: T)

function CountFrequencyRcr(s: seq<char>, key: char): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountFrequencyRcr(s[..|s|-1], key) + if (s[|s|-1] == key) then
            1
        else
            0
}

predicate CheckFirstRepeatedChar(str1: seq<char>, repeated_char: Option<(nat, char)>)
{
    match repeated_char
    case None =>
        forall k :: 0 <= k < |str1| ==> CountFrequencyRcr(str1, str1[k]) <= 1
    case Some(pair) =>
        var idx := pair.0;
        var rp_char := pair.1;
        && idx as int <= |str1|
        && (forall i :: 0 <= i < idx as int ==> CountFrequencyRcr(str1, str1[i]) <= 1)
        && CountFrequencyRcr(str1, rp_char) > 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma to establish equality between full sequence counting */
lemma CountFrequencyIncrement(s: seq<char>, key: char, i: nat)
  requires i < |s|
  ensures CountFrequencyRcr(s[..i+1], key) == CountFrequencyRcr(s[..i], key) + (if s[i] == key then 1 else 0)
{
  var prefix := s[..i+1];
  var prevPrefix := s[..i];
  assert prefix == prevPrefix + [s[i]];
  assert |prefix| == i + 1;
  if i == 0 {
    assert prevPrefix == [];
    assert CountFrequencyRcr(prevPrefix, key) == 0;
    assert prefix == [s[0]];
  }
}

lemma CountFrequencySubsequence(s: seq<char>, key: char, i: nat, j: nat)
  requires i <= j <= |s|
  ensures CountFrequencyRcr(s[..i], key) <= CountFrequencyRcr(s[..j], key)
{
  if i == j {
    assert s[..i] == s[..j];
  } else {
    CountFrequencySubsequence(s, key, i, j-1);
    assert s[..j] == s[..j-1] + [s[j-1]];
  }
}

lemma CountFrequencyFullSeq(s: seq<char>, key: char, i: nat)
  requires i <= |s|
  ensures CountFrequencyRcr(s[..i], key) <= CountFrequencyRcr(s, key)
{
  assert s == s[..|s|];
  CountFrequencySubsequence(s, key, i, |s|);
}

lemma CountFrequencyFullSeqEqual(s: seq<char>, key: char)
  ensures CountFrequencyRcr(s[..|s|], key) == CountFrequencyRcr(s, key)
{
  assert s == s[..|s|];
}
// </vc-helpers>

// <vc-spec>
method FirstRepeatedChar(str1: array<char>) returns (repeated_char: Option<(nat, char)>)
    ensures CheckFirstRepeatedChar(str1[..], repeated_char)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed assertion by using lemma to establish sequence equality */
{
  var i := 0;
  
  while i < str1.Length
    invariant 0 <= i <= str1.Length
    invariant forall k :: 0 <= k < i ==> CountFrequencyRcr(str1[..], str1[k]) <= 1
  {
    var c := str1[i];
    var count := 0;
    var j := 0;
    
    // Count occurrences of c up to and including position i
    while j <= i
      invariant 0 <= j <= i + 1
      invariant count == CountFrequencyRcr(str1[..j], c)
    {
      if str1[j] == c {
        count := count + 1;
      }
      CountFrequencyIncrement(str1[..], c, j);
      j := j + 1;
    }
    
    assert j == i + 1;
    assert count == CountFrequencyRcr(str1[..i+1], c);
    
    if count > 1 {
      // Found a repeated character
      CountFrequencyFullSeq(str1[..], c, i+1);
      assert CountFrequencyRcr(str1[..], c) >= count;
      assert CountFrequencyRcr(str1[..], c) > 1;
      repeated_char := Some((i, c));
      return;
    }
    
    // This character appears only once up to position i+1
    assert count <= 1;
    
    // Check if this character appears later in the string
    var totalCount := count;
    var k := i + 1;
    while k < str1.Length
      invariant i + 1 <= k <= str1.Length
      invariant totalCount == CountFrequencyRcr(str1[..k], c)
    {
      if str1[k] == c {
        totalCount := totalCount + 1;
      }
      CountFrequencyIncrement(str1[..], c, k);
      k := k + 1;
    }
    
    assert k == str1.Length;
    assert totalCount == CountFrequencyRcr(str1[..str1.Length], c);
    CountFrequencyFullSeqEqual(str1[..], c);
    assert totalCount == CountFrequencyRcr(str1[..], c);
    
    if totalCount > 1 {
      // This character is repeated later
      repeated_char := Some((i, c));
      return;
    }
    
    // This character appears only once in the entire string
    assert CountFrequencyRcr(str1[..], c) <= 1;
    i := i + 1;
  }
  
  repeated_char := None;
}
// </vc-code>
