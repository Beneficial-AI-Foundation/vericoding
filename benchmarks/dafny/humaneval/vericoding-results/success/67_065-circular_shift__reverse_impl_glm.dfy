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
method reverse(str: string) returns (rev: string)

    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
// </vc-spec>
// <vc-code>
{
  var len := |str|;
  var chars := new char[len];
  for i := 0 to len
    invariant 0 <= i <= len
    invariant forall j :: 0 <= j < i ==> chars[j] == str[len - 1 - j]
  {
    if i < len {
      chars[i] := str[len - 1 - i];
    }
  }
  rev := chars[..];
}
// </vc-code>
