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
function reverseHelper(s: string, idx: int): char
  requires 0 <= idx < |s|
{
  s[|s| - 1 - idx]
}

lemma ReverseIndexLemma(s: string, k: int)
  requires 0 <= k < |s|
  ensures |s| - 1 - k >= 0
  ensures |s| - 1 - k < |s|
{
}

lemma LengthInvariantLemma(rev: string, i: int, str: string)
  requires |rev| == i
  requires i <= |str|
  ensures |rev| <= |str|
{
}

lemma CharacterPreservationLemma(rev: string, str: string, i: int, k: int, c: char)
  requires 0 <= k < i
  requires |rev| == i
  requires i <= |str|
  requires rev[k] == str[|str| - 1 - k]
  ensures (rev + [c])[k] == str[|str| - 1 - k]
{
  StringAppendLemma(rev, c, k);
}

lemma StringAppendLemma(s: string, c: char, k: int)
  requires 0 <= k < |s|
  ensures (s + [c])[k] == s[k]
{
}

lemma StringAppendLastLemma(s: string, c: char)
  ensures |s + [c]| == |s| + 1
  ensures (s + [c])[|s|] == c
{
}

lemma ReverseIndexPreservation(s: string, i: int)
  requires 0 <= i < |s|
  ensures |s| - 1 - i >= 0
  ensures |s| - 1 - i < |s|
{
}

// </vc-helpers>

// <vc-spec>
method reverse(str: string) returns (rev: string)

    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed index bounds in verification */
  rev := "";
  var i := 0;
  
  while i < |str|
    invariant |rev| == i
    invariant i <= |str|
    invariant forall k | 0 <= k < i :: rev[k] == str[|str| - 1 - k]
  {
    ReverseIndexPreservation(str, i);
    var c := str[|str| - 1 - i];
    var old_rev := rev;
    rev := rev + [c];
    
    // Prove invariant preservation for all existing elements
    var k := 0;
    while k < i
      invariant 0 <= k <= i
      invariant forall j | 0 <= j < k :: rev[j] == old_rev[j] == str[|str| - 1 - j]
      invariant |rev| == i + 1
    {
      StringAppendLemma(old_rev, c, k);
      k := k + 1;
    }
    
    // Prove the new element is correct
    StringAppendLastLemma(old_rev, c);
    
    i := i + 1;
  }
  LengthInvariantLemma(rev, i, str);
}
// </vc-code>
