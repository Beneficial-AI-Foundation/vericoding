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
lemma stringNatPreservedByConstruction(s: string)
  requires |s| > 0 && (|s| > 1 ==> s[0] != '0') && forall i | 0 <= i < |s| :: s[i] in "0123456789"
  ensures s as stringNat == s
{
}

lemma reversePreservesStringNat(s: stringNat) 
  ensures var rev := reverseString(s); rev as stringNat == rev
{
  var rev := reverseString(s);
  assert |rev| == |s| > 0;
  if |rev| > 1 {
    assert rev[0] == s[|s| - 1];
    assert s[|s| - 1] in "0123456789";
  }
  assert forall i | 0 <= i < |rev| :: rev[i] in "0123456789";
  if |rev| > 1 {
    assert rev[0] == s[|s| - 1];
    if s == "0" {
      assert |s| == 1;
      assert |rev| == 1;
    } else {
      assert s[|s| - 1] != '0' || |s| == 1;
    }
  }
}

function reverseString(s: string): string
  ensures |reverseString(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverseString(s)[k] == s[|s| - 1 - k]
{
  if |s| == 0 then ""
  else reverseString(s[1..]) + [s[0]]
}

lemma slicePreservesStringNat(s: stringNat, i: nat, j: nat)
  requires 0 <= i <= j <= |s|
  requires j > i
  requires i == 0 || s[0] != '0' || j - i == 1
  ensures var slice := s[i..j]; |slice| > 0 ==> (|slice| > 1 ==> slice[0] != '0') && forall k | 0 <= k < |slice| :: slice[k] in "0123456789"
{
}

lemma concatenationPreservesStringNat(s1: string, s2: string)
  requires |s1| > 0 && |s2| > 0
  requires forall i | 0 <= i < |s1| :: s1[i] in "0123456789"
  requires forall i | 0 <= i < |s2| :: s2[i] in "0123456789"
  requires s1[0] != '0' || |s1| == 1
  ensures var concat := s1 + s2; |concat| > 0 && (|concat| > 1 ==> concat[0] != '0') && forall i | 0 <= i < |concat| :: concat[i] in "0123456789"
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
  if shift > |s| {
    shifted := reverseString(s);
    reversePreservesStringNat(s);
  } else {
    var rightPart := s[|s| - shift..];
    var leftPart := s[..|s| - shift];
    shifted := rightPart + leftPart;
    
    if shift == 0 {
      assert rightPart == "";
      assert leftPart == s;
      assert shifted == s;
    } else if shift == |s| {
      assert rightPart == s;
      assert leftPart == "";
      assert shifted == s;
    } else {
      assert |rightPart| > 0;
      assert |leftPart| > 0;
      slicePreservesStringNat(s, |s| - shift, |s|);
      slicePreservesStringNat(s, 0, |s| - shift);
      if |rightPart| > 0 && |leftPart| > 0 {
        concatenationPreservesStringNat(rightPart, leftPart);
      }
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