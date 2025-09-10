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
// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: seq<char>) returns (result: seq<char>)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
var result: seq<char> := [];
if |s| > 0 {
  result := [s[0]];
}
var i := 1;
while i < |s|
  invariant 1 <= i <= |s|
  invariant |result| > 0 || |s| == 0
  invariant |result| <= i <= |s|
  invariant |s| > 0 ==> |result| > 0
  invariant |s| > 0 ==> result[0] == s[0]
  invariant NoConsecutiveVowels(result)
{
  if !( |result| > 0 && IsVowel(result[|result|-1]) && IsVowel(s[i]) ) {
    result := result + [s[i]];
  }
  i := i + 1;
}
// </vc-code>

