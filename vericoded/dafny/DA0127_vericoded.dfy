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
function toString(n: int): string

lemma CountFlipsIterative(s: string, k: int)
  requires 0 <= k <= |s|
  ensures CountFlipsUpTo(s, k) == |set i | 0 <= i < k && NeedsFlipping(s[i])|
{
  if k == 0 {
    assert (set i | 0 <= i < 0 && NeedsFlipping(s[i])) == {};
  } else {
    CountFlipsIterative(s, k - 1);
    var prevSet := set i | 0 <= i < k - 1 && NeedsFlipping(s[i]);
    var currSet := set i | 0 <= i < k && NeedsFlipping(s[i]);
    
    if NeedsFlipping(s[k - 1]) {
      assert currSet == prevSet + {k - 1};
    } else {
      assert currSet == prevSet;
    }
  }
}

function CountFlipsUpTo(s: string, k: int): int
  requires 0 <= k <= |s|
{
  if k == 0 then 0
  else if NeedsFlipping(s[k - 1]) then CountFlipsUpTo(s, k - 1) + 1
  else CountFlipsUpTo(s, k - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
  requires |s| >= 1 && |s| <= 50
  ensures |result| > 0
  ensures result == toString(CountFlips(s)) + "\n"
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == CountFlipsUpTo(s, i)
  {
    if NeedsFlipping(s[i]) {
      count := count + 1;
    }
    i := i + 1;
  }
  
  CountFlipsIterative(s, |s|);
  assert count == CountFlips(s);
  
  result := toString(count) + "\n";
}
// </vc-code>

