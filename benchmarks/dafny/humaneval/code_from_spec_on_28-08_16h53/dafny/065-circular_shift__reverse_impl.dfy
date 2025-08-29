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
lemma ReverseLength(s: string)
  ensures |reverse_helper(s)| == |s|
{
  if s == "" {
  } else {
    ReverseLength(s[1..]);
  }
}

lemma ReverseCorrectness(s: string, i: int)
  requires 0 <= i < |s|
  ensures reverse_helper(s)[i] == s[|s| - 1 - i]
{
  if s == "" {
  } else {
    var rest := reverse_helper(s[1..]);
    if i < |rest| {
      ReverseCorrectness(s[1..], i);
    }
  }
}

function reverse_helper(s: string): string
{
  if s == "" then ""
  else reverse_helper(s[1..]) + [s[0]]
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method reverse(str: string) returns (rev: string)
Reverse order. Ensures: returns the correct size/count; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method reverse(str: string) returns (rev: string)
  ensures |rev| == |str|
  ensures forall i :: 0 <= i < |str| ==> rev[i] == str[|str| - 1 - i]
// </vc-spec>
// <vc-code>
method reverse(str: string) returns (rev: string)
  ensures |rev| == |str|
  ensures forall i :: 0 <= i < |str| ==> rev[i] == str[|str| - 1 - i]
{
  rev := reverse_helper(str);
  ReverseLength(str);
  forall i | 0 <= i < |str|
    ensures rev[i] == str[|str| - 1 - i]
  {
    ReverseCorrectness(str, i);
  }
}
// </vc-code>
