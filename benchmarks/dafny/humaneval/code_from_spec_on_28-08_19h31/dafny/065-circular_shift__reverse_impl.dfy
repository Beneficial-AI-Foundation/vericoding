type stringNat = s: string |
  |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
  forall i | 0 <= i < |s| :: s[i] in "0123456789"
  witness "1"
function natToString(n: nat): stringNat {
  match n
    case 0 => "0" case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4"
    case 5 => "5" case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
    case _ => natToString(n / 10) + natToString(n % 10)
}
method circular_shift(a: nat, shift: nat) returns (shifted: string)
  // post-conditions-start
  ensures |shifted| == |natToString(a)|
  ensures var s := natToString(a); shift > |s| ==> forall i :: 0 <= i < |s| ==> shifted[i] == s[|s| - 1 - i]
  ensures var s := natToString(a); shift <= |s| ==> shifted == s[|s| - shift..] + s[..|s| - shift]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function reverseString(s: string): string
{
  if |s| == 0 then "" else reverseString(s[1..]) + s[0..1]
}

lemma ReverseProperties(s: string)
  ensures |reverseString(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverseString(s)[k] == s[|s| - 1 - k]
{
  if |s| == 0 {
  } else {
    calc {
      reverseString(s);
      reverseString(s[1..]) + s[0..1];
    }
    ReverseProperties(s[1..]);
    assert |reverseString(s[1..])| == |s[1..]|;
    assert |s[1..]| == |s| - 1;
    assert |reverseString(s)| == |s| - 1 + 1 == |s|;
    forall k | 0 <= k < |s|
      ensures reverseString(s)[k] == s[|s| - 1 - k]
    {
      if k < |s| - 1 {
        assert reverseString(s)[k] == reverseString(s[1..])[k];
        assert reverseString(s[1..])[k] == s[1..][|s[1..]| - 1 - k];
        assert |s[1..]| == |s| - 1;
        assert s[1..][(|s| - 1) - 1 - k] == s[1..][|s| - 2 - k];
        assert s[1..][|s| - 2 - k] == s[1 + (|s| - 2 - k)];
        assert 1 + (|s| - 2 - k) == |s| - 1 - k;
        assert s[|s| - 1 - k] == s[|s| - 1 - k];
      } else {
        assert k == |s| - 1;
        assert reverseString(s)[k] == s[0..1][0];
        assert s[0..1][0] == s[0];
        assert s[|s| - 1 - k] == s[|s| - 1 - (|s| - 1)] == s[0];
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  rev := "";
  var i := |str| - 1;
  while i >= 0
    decreases i
    invariant -1 <= i < |str|
    invariant |rev| == |str| - 1 - i
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == str[|str| - 1 - k]
  {
    rev := rev + str[i..i+1];
    i := i - 1;
  }
}
// </vc-code>
