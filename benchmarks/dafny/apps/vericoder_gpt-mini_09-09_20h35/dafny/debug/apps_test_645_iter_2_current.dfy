predicate IsVowel(c: char) {
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

predicate IsOddDigit(c: char) {
  c == '1' || c == '3' || c == '5' || c == '7' || c == '9'
}

predicate NeedsFlipping(c: char) {
  IsVowel(c) || IsOddDigit(c)
}

function CountFlips(s: string): int {
  |set i | 0 <= i < |s| && NeedsFlipping(s[i])|
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
  requires |s| >= 1 && |s| <= 50
  ensures |result| > 0
  ensures result == toString(CountFlips(s)) + "\n"
// </vc-spec>
// <vc-code>
{
  ghost var seen: set<int> := {};
  var cnt := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant seen == { k | 0 <= k < i && NeedsFlipping(s[k]) }
    invariant cnt == |seen|
  {
    if NeedsFlipping(s[i]) {
      seen := seen + {i};
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  assert cnt == CountFlips(s);
  result := toString(cnt) + "\n";
}
// </vc-code>

