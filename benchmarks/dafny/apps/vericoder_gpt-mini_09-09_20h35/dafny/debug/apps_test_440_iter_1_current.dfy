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
  var res: seq<char> := [];
  var i := 0;
  while i < |s|
    decreases |s| - i
    invariant 0 <= i <= |s|;
    invariant |res| <= i;
    invariant NoConsecutiveVowels(res);
    invariant i > 0 ==> |res| > 0 && res[0] == s[0];
  {
    if i == 0 {
      // first character must be kept when s is non-empty
      res := res + [s[0]];
    } else {
      var c := s[i];
      // only append if it does not create consecutive vowels
      if !(IsVowel(c) && IsVowel(res[|res|-1])) {
        res := res + [c];
      }
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>

