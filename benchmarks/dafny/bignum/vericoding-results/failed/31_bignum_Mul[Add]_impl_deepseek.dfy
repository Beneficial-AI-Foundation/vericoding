ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
// Fixed RemoveLeadingZeros to return proper string type
function RemoveLeadingZeros(s: string): string
  requires ValidBitString(s)
  ensures ValidBitString(RemoveLeadingZeros(s))
  ensures |RemoveLeadingZeros(s)| <= |s|
  ensures Str2Int(RemoveLeadingZeros(s)) == Str2Int(s)
  decreases s
{
  if |s| == 0 then s
  else if s[0] == '0' then 
    RemoveLeadingZeros(s[1..])
  else s
}

// Fixed PadZeros to properly handle recursion with lemma support
ghost function PadZeros(s: string, n: nat): string
  requires ValidBitString(s)
  requires n >= |s|
  ensures ValidBitString(PadZeros(s, n))
  ensures |PadZeros(s, n)| == n
  ensures Str2Int(PadZeros(s, n)) == Str2Int(s)
  decreases n - |s|
{
  if n == |s| then s
  else {
    var prepended := "0" + s;
    assert Str2Int(prepended) == Str2Int(s);
    PadZeros(prepended, n)
  }
}

// Added Power2 function
function Power2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}

// Fixed ShiftLeft to be more efficient and correct
function ShiftLeft(s: string, n: nat): string
  requires ValidBitString(s)
  ensures ValidBitString(ShiftLeft(s, n))
  ensures |ShiftLeft(s, n)| == |s| + n
  ensures Str2Int(ShiftLeft(s, n)) == Str2Int(s) * Power2(n)
  decreases n
{
  if n == 0 then s
  else ShiftLeft(s + "0", n - 1)
}

// Added AddHelper function
function AddHelper(s1: string, s2: string, carry: nat): string
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2|
  requires carry <= 1
  ensures ValidBitString(AddHelper(s1, s2, carry))
  ensures |AddHelper(s1, s2, carry)| == |s1| + 1 || |AddHelper(s1, s2, carry)| == |s1|
  ensures Str2Int(AddHelper(s1, s2, carry)) == Str2Int(s1) + Str2Int(s2) + carry
  decreases |s1|
{
  if |s1| == 0 then
    if carry == 1 then "1" else ""
  else
    var s1_last := if s1[|s1|-1] == '1' then 1 else 0;
    var s2_last := if s2[|s2|-1] == '1' then 1 else 0;
    var sum := s1_last + s2_last + carry;
    var new_carry := sum / 2;
    var digit := if sum % 2 == 1 then "1" else "0";
    AddHelper(s1[0..|s1|-1], s2[0..|s2|-1], new_carry) + digit
}

// Added Max function
function Max(a: nat, b: nat): nat
{
  if a > b then a else b
}

// Added lemma to help verify PadZeros
lemma PadZerosPreservesValue(s: string, n: nat)
  requires ValidBitString(s)
  requires n >= |s|
  ensures Str2Int(PadZeros(s, n)) == Str2Int(s)
  decreases n - |s|
{
  if n > |s| {
    var prepended := "0" + s;
    assert Str2Int(prepended) == Str2Int(s);
    PadZerosPreservesValue(prepended, n);
  }
}

// Added lemma for AddHelper
lemma AddHelperPreservesValue(s1: string, s2: string, carry: nat)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires |s1| == |s2|
  requires carry <= 1
  ensures Str2Int(AddHelper(s1, s2, carry)) == Str2Int(s1) + Str2Int(s2) + carry
  decreases |s1|
{
  if |s1| > 0 {
    var s1_last := if s1[|s1|-1] == '1' then 1 else 0;
    var s2_last := if s2[|s2|-1] == '1' then 1 else 0;
    var sum := s1_last + s2_last + carry;
    var new_carry := sum / 2;
    
    AddHelperPreservesValue(s1[0..|s1|-1], s2[0..|s2|-1], new_carry);
  }
}

// Added lemma for zero padding equivalence
lemma ZeroPrefixLemma(s: string)
  requires ValidBitString(s)
  ensures Str2Int("0" + s) == Str2Int(s)
{
  if |s| > 0 {
    ZeroPrefixLemma(s[0..|s|-1]);
  }
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var len1 := |s1|;
  var len2 := |s2|;
  res := "0";
  
  ghost var res_ghost : string := "0";
  
  var i := len1;
  while (i > 0)
    decreases i
    invariant 0 <= i <= len1
    invariant ValidBitString(res)
    invariant res_ghost == RemoveLeadingZeros(res)
    invariant Str2Int(res_ghost) == Str2Int(s1[i..]) * Str2Int(s2)
  {
    i := i - 1;
    var shifted := ShiftLeft(s2, len1 - 1 - i);
    
    ZeroPrefixLemma(s1[i+1..]);
    
    if s1[i] == '1' {
      var old_res := res;
      var old_ghost := res_ghost;
      
      res := Add(res, shifted);
      
      // Update ghost variable
      var max_len := Max(|old_res|, |shifted|) + 1;
      ghost var padded_res := PadZeros(old_res, max_len);
      ghost var padded_shifted := PadZeros(shifted, max_len);
      ghost var sum := AddHelper(padded_res, padded_shifted, 0);
      res_ghost := RemoveLeadingZeros(sum);
      
      assert Str2Int(padded_res) == Str2Int(old_res);
      assert Str2Int(padded_shifted) == Str2Int(shifted);
      assert Str2Int(sum) == Str2Int(padded_res) + Str2Int(padded_shifted);
      assert Str2Int(res_ghost) == Str2Int(old_res) + Str2Int(shifted);
      assert Str2Int(shifted) == Str2Int(s2) * Power2(len1 - 1 - i);
      assert Str2Int(res_ghost) == Str2Int(s1[i+1..]) * Str2Int(s2) + Str2Int(s2) * Power2(len1 - 1 - i);
      assert Str2Int(res_ghost) == Str2Int(s2) * (Str2Int(s1[i+1..]) + Power2(len1 - 1 - i));
      assert Str2Int(s1[i..]) == Str2Int(s1[i+1..]) + (if s1[i] == '1' then Power2(len1 - 1 - i) else 0);
    } else {
      res_ghost := RemoveLeadingZeros(res);
      assert Str2Int(res_ghost) == Str2Int(s1[i+1..]) * Str2Int(s2);
    }
  }
  res := RemoveLeadingZeros(res);
}
// </vc-code>

