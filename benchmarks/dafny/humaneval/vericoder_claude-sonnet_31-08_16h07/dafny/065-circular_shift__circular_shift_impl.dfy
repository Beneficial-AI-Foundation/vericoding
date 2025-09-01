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

// <vc-helpers>
lemma stringNatProperties(s: stringNat)
  ensures |s| > 0
  ensures |s| > 1 ==> s[0] != '0'
  ensures forall i | 0 <= i < |s| :: s[i] in "0123456789"
{
}

lemma natToStringProperties(n: nat)
  ensures var s := natToString(n); |s| > 0
  ensures var s := natToString(n); |s| > 1 ==> s[0] != '0'
  ensures var s := natToString(n); forall i | 0 <= i < |s| :: s[i] in "0123456789"
{
}

lemma stringSliceProperties(s: string, i: nat, j: nat)
  requires 0 <= i <= j <= |s|
  ensures |s[i..j]| == j - i
{
}

lemma stringConcatProperties(s1: string, s2: string)
  ensures |s1 + s2| == |s1| + |s2|
{
}
// </vc-helpers>

// <vc-spec>
method circular_shift(a: nat, shift: nat) returns (shifted: string)
  // post-conditions-start
  ensures |shifted| == |natToString(a)|
  ensures var s := natToString(a); shift > |s| ==> forall i :: 0 <= i < |s| ==> shifted[i] == s[|s| - 1 - i]
  ensures var s := natToString(a); shift <= |s| ==> shifted == s[|s| - shift..] + s[..|s| - shift]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var s := natToString(a);
  natToStringProperties(a);
  
  if shift > |s| {
    shifted := reverse(s);
  } else {
    var left := s[|s| - shift..];
    var right := s[..|s| - shift];
    stringSliceProperties(s, |s| - shift, |s|);
    stringSliceProperties(s, 0, |s| - shift);
    shifted := left + right;
    stringConcatProperties(left, right);
  }
}
// </vc-code>

method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
{
  assume{:axiom} false;
}