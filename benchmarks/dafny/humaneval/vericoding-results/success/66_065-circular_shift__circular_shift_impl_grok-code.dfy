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
/* helper modified by LLM (iteration 4): fixed syntax in reverseLemma assert statement by replacing :: with ==> */
function reverse(s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else [s[|s|-1]] + reverse(s[..|s|-1])
}

lemma reverseLemma(s: string)
  ensures |reverse(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> reverse(s)[i] == s[|s|-1 - i]
{
  if |s| > 0 {
    var rev_suffix := reverse(s[..|s|-1]);
    reverseLemma(s[..|s|-1]);
    assert forall j :: 0 <= j < |rev_suffix| ==> rev_suffix[j] == s[..|s|-1][|s|-2 - j];
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
/* code modified by LLM (iteration 4): no changes, verified implementation with proper lemma call */
{
  var s := natToString(a);
  var len := |s|;
  if shift > len {
    shifted := reverse(s);
    reverseLemma(s);
  } else {
    shifted := s[len - shift ..] + s[.. len - shift];
  }
}
// </vc-code>
