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

// </vc-helpers>

// <vc-spec>
method circular_shift(a: nat, shift: nat) returns (shifted: string)

  ensures |shifted| == |natToString(a)|
  ensures var s := natToString(a); shift > |s| ==> forall i :: 0 <= i < |s| ==> shifted[i] == s[|s| - 1 - i]
  ensures var s := natToString(a); shift <= |s| ==> shifted == s[|s| - shift..] + s[..|s| - shift]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed compilation error by converting char to string. */
  var s := natToString(a);
  var len := |s|;
  if shift > len {
    shifted := "";
    var i := 0;
    while i < len
      invariant 0 <= i <= len
      invariant |shifted| == i
      invariant forall j :: 0 <= j < i ==> shifted[j] == s[len - 1 - j]
    {
      shifted := shifted + s[len - 1 - i .. len - i]; // Convert char to string slice
      i := i + 1;
    }
  }
  else {
    shifted := s[len - shift ..] + s[.. len - shift];
  }
}
// </vc-code>
