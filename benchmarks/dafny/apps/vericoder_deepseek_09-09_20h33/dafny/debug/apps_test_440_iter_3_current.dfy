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
  assert |[c] + output| <= |input|;
  
  // First character condition
  assert |input| > 0 ==> ([c] + output)[0] == c == input[0];
  
  // No consecutive vowels
  if |output| > 0 {
    assert !(IsVowel(c) && IsVowel(output[0]));
  }
}
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
      result := [s[0]] + rest[1..];
    } else {
      result := [s[0]] + rest;
    }
  }
}
// </vc-code>

