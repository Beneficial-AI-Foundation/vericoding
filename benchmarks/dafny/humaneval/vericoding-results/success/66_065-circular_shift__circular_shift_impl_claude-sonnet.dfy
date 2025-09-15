// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed reverseString function to ensure proper indexing */
function reverseString(s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else reverseString(s[1..]) + [s[0]]
}

lemma reverseStringLength(s: string)
  ensures |reverseString(s)| == |s|
{
  if |s| == 0 {
  } else {
    reverseStringLength(s[1..]);
  }
}

lemma reverseStringCorrectness(s: string, i: int)
  requires 0 <= i < |s|
  ensures |reverseString(s)| == |s|
  ensures reverseString(s)[i] == s[|s| - 1 - i]
{
  reverseStringLength(s);
  if |s| == 1 {
    assert i == 0;
    assert reverseString(s) == [s[0]];
  } else {
    var tail := s[1..];
    var revTail := reverseString(tail);
    reverseStringLength(tail);
    
    if i == |s| - 1 {
      assert reverseString(s) == revTail + [s[0]];
      assert reverseString(s)[i] == s[0];
      assert s[|s| - 1 - i] == s[0];
    } else {
      assert 0 <= i < |s| - 1;
      assert reverseString(s) == revTail + [s[0]];
      assert reverseString(s)[i] == revTail[i];
      reverseStringCorrectness(tail, i);
      assert revTail[i] == tail[|tail| - 1 - i];
      assert tail[|tail| - 1 - i] == s[|s| - 1 - i];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method circular_shift(a: nat, shift: nat) returns (shifted: string)

  ensures |shifted| == |natToString(a)|
  ensures var s := natToString(a); shift > |s| ==> forall i :: 0 <= i < |s| ==> shifted[i] == s[|s| - 1 - i]
  ensures var s := natToString(a); shift <= |s| ==> shifted == s[|s| - shift..] + s[..|s| - shift]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): use individual correctness lemma for each index */
  var s := natToString(a);
  if shift > |s| {
    shifted := reverseString(s);
    reverseStringLength(s);
    forall i | 0 <= i < |s| {
      reverseStringCorrectness(s, i);
    }
  } else {
    shifted := s[|s| - shift..] + s[..|s| - shift];
  }
}
// </vc-code>
