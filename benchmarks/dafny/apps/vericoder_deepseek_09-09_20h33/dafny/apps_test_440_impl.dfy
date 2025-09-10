predicate IsVowel(c: char)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y'
}

predicate NoConsecutiveVowels(s: seq<char>)
{
    forall i :: 0 <= i < |s| - 1 ==> !(IsVowel(s[i]) && IsVowel(s[i+1]))
}

predicate ValidOutput(input: seq<char>, output: seq<char>)
{
    |output| <= |input| &&
    NoConsecutiveVowels(output) &&
    (|input| > 0 ==> |output| > 0) &&
    (|input| > 0 ==> output[0] == input[0])
}

// <vc-helpers>
lemma {:induction false} LemmaNoConsecutiveVowelsAppend(s: seq<char>, c: char)
  requires NoConsecutiveVowels(s)
  ensures !(|s| > 0 && IsVowel(s[|s|-1]) && IsVowel(c)) ==> NoConsecutiveVowels(s + [c])
{
}

lemma {:induction false} LemmaConsValid(input: seq<char>, output: seq<char>, c: char)
  requires ValidOutput(input, output) && |input| > 0
  requires c == input[0]
  requires !(|output| > 0 && IsVowel(output[|output|-1]) && IsVowel(c))
  ensures ValidOutput(input, [c] + output)
  decreases |input|
{
  // Length condition
  assert |[c] + output| == 1 + |output|;
  
  // Fix: Use appropriate length relationship
  var tail := input[1..];
  assert |tail| == |input| - 1;
  
  // Since output is valid for tail, we know |output| <= |tail| = |input| - 1
  // So 1 + |output| <= 1 + (|input| - 1) = |input|
  assert |[c] + output| <= |input|;
  
  // First character condition
  assert ([c] + output)[0] == c == input[0];
  
  // No consecutive vowels between first character and first character of output
  if |output| > 0 {
    assert !(IsVowel(c) && IsVowel(output[0]));
  }
  
  // Check the no consecutive vowels for the entire sequence
  assert NoConsecutiveVowels([c] + output);
}

lemma {:induction false} LemmaHandleConsecutiveVowels(s: seq<char>, rest: seq<char>) 
  requires ValidOutput(s[1..], rest) && |s| > 0
  requires IsVowel(s[0]) && |rest| > 0 && IsVowel(rest[0])
  ensures ValidOutput(s, [s[0]] + rest[1..])
{
  // Length condition
  assert |[s[0]] + rest[1..]| == 1 + |rest[1..]|;
  assert |rest[1..]| == |rest| - 1;
  
  // Since rest is valid for s[1..], we know |rest| <= |s[1..]| = |s| - 1
  // So 1 + (|rest| - 1) = |rest| <= |s| - 1 < |s|
  assert |[s[0]] + rest[1..]| <= |s|;
  
  // First character condition
  assert ([s[0]] + rest[1..])[0] == s[0];
  
  // Check no consecutive vowels
  if |rest[1..]| > 0 {
    // We need to check that adding s[0] doesn't create consecutive vowels
    assert !(IsVowel(s[0]) && IsVowel(rest[1..][0]));
  }
  
  // The rest of rest[1..] already has no consecutive vowels (by ValidOutput)
  assert NoConsecutiveVowels([s[0]] + rest[1..]);
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: seq<char>) returns (result: seq<char>)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    result := [];
  } else {
    var rest := solve(s[1..]);
    
    if |rest| == 0 {
      result := [s[0]];
    } else if IsVowel(s[0]) && IsVowel(rest[0]) {
      // Handle consecutive vowels by skipping the next vowel
      LemmaHandleConsecutiveVowels(s, rest);
      result := [s[0]] + rest[1..];
    } else {
      LemmaConsValid(s, rest, s[0]);
      result := [s[0]] + rest;
    }
  }
}
// </vc-code>

