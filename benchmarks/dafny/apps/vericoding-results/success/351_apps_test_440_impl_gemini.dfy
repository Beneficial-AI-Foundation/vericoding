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
    result := [s[0]];
    var i := 1;
    while i < |s|
      invariant 1 <= i <= |s|
      invariant ValidOutput(s[0..i], result)
    {
      if !IsVowel(result[|result|-1]) || !IsVowel(s[i]) {
        result := result + [s[i]];
      }
      i := i + 1;
    }
  }
}
// </vc-code>

