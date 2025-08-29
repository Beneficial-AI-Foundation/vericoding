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
lemma natToStringProperties(n: nat)
  ensures var s := natToString(n); |s| > 0
  ensures var s := natToString(n); forall i | 0 <= i < |s| :: s[i] in "0123456789"
{
}

lemma natToStringWellFormed(n: nat)
  ensures natToString(n) is stringNat
{
  natToStringProperties(n);
}

lemma stringConcatProperties(s1: string, s2: string)
  requires forall i | 0 <= i < |s1| :: s1[i] in "0123456789"
  requires forall i | 0 <= i < |s2| :: s2[i] in "0123456789"
  ensures forall i | 0 <= i < |s1 + s2| :: (s1 + s2)[i] in "0123456789"
{
}

lemma stringSliceProperties(s: string, start: int, end: int)
  requires 0 <= start <= end <= |s|
  requires forall i | 0 <= i < |s| :: s[i] in "0123456789"
  ensures forall i | 0 <= i < |s[start..end]| :: s[start..end][i] in "0123456789"
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method circular_shift(a: nat, shift: nat) returns (shifted: string)
Process input. Ensures: returns the correct size/count; the condition holds for all values; returns the correct size/count.
*/
// </vc-description>

// <vc-spec>
method circular_shift(a: nat, shift: nat) returns (shifted: string)
  ensures |shifted| > 0
  ensures forall i | 0 <= i < |shifted| :: shifted[i] in "0123456789"
  ensures |shifted| == |natToString(a)|
// </vc-spec>
// <vc-code>
method circular_shift(a: nat, shift: nat) returns (shifted: string)
  ensures |shifted| > 0
  ensures forall i | 0 <= i < |shifted| :: shifted[i] in "0123456789"
  ensures |shifted| == |natToString(a)|
{
  var str := natToString(a);
  natToStringWellFormed(a);
  
  if |str| <= 1 || shift == 0 {
    shifted := str;
  } else {
    var effectiveShift := shift % |str|;
    if effectiveShift == 0 {
      shifted := str;
    } else {
      var splitPoint := |str| - effectiveShift;
      var leftPart := str[splitPoint..];
      var rightPart := str[..splitPoint];
      
      stringSliceProperties(str, splitPoint, |str|);
      stringSliceProperties(str, 0, splitPoint);
      stringConcatProperties(leftPart, rightPart);
      
      shifted := leftPart + rightPart;
    }
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