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
// No additional helpers needed for this task
// </vc-helpers>

// <vc-description>
/*
function_signature: method circular_shift(a: nat, shift: nat) returns (shifted: string)
Process input. Ensures: returns the correct size/count; the condition holds for all values; returns the correct size/count.
*/
// </vc-description>

// <vc-spec>
method circular_shift(a: nat, shift: nat) returns (shifted: string)
  requires a >= 0
  requires shift >= 0
  ensures |shifted| == |natToString(a)|
  ensures forall k :: 0 <= k < |shifted| ==> shifted[k] in "0123456789"
  ensures shifted == natToString(a)[(shift % |natToString(a)|)..] + natToString(a)[..(shift % |natToString(a)|)]
// </vc-spec>
// <vc-code>
{
  var str := natToString(a);
  var len := |str|;
  var effectiveShift := shift % len;
  if effectiveShift == 0 {
    return str;
  }
  var result := str[effectiveShift..] + str[..effectiveShift];
  return result;
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