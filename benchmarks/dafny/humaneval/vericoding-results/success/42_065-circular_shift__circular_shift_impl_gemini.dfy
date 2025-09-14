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
/* helper modified by LLM (iteration 3): kept as is, seems correct for reverse properties */
function reverse(s: string): string
  decreases |s|
{
  if |s| == 0 then "" else s[|s|-1..] + reverse(s[..|s|-1])
}

lemma ReverseProperties(s: string)
  ensures |reverse(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> reverse(s)[i] == s[|s|-1-i]
  decreases |s|
{
  if |s| > 0 {
    ReverseProperties(s[..|s|-1]);
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
  /* code modified by LLM (iteration 3): simplified the rotation logic to avoid timeouts */
  var s := natToString(a);
  var n := |s|;

  if shift > n {
    ReverseProperties(s);
    shifted := reverse(s);
  } else {
    shifted := s[n - shift..] + s[..n - shift];
  }
}
// </vc-code>
