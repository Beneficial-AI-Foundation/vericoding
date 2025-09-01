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
lemma ReverseCharacterMapping(str: string, rev: string, k: int)
    requires |rev| == |str|
    requires forall i :: 0 <= i < |str| ==> rev[i] == str[|str| - 1 - i]
    requires 0 <= k < |str|
    ensures rev[k] == str[|str| - 1 - k]
{
}

lemma ReverseLength(str: string, rev: string)
    requires |rev| == |str|
    ensures |rev| == |str|
{
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
    var i := 0;
    while i < |str|
        invariant 0 <= i <= |str|
        invariant |rev| == i
        invariant forall k :: 0 <= k < i ==> rev[k] == str[|str| - 1 - k]
    {
        rev := rev + [str[|str| - 1 - i]];
        i := i + 1;
    }
}
// </vc-code>

