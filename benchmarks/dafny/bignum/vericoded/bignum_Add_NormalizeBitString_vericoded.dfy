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

method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  // I added and proved some extra post-conditions:
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{
}

lemma Str2IntSingle(c: char)
  requires c == '0' || c == '1'
  ensures Str2Int([c]) == if c == '1' then 1 else 0
{
  var s := [c];
  assert s[0..0] == [];
  assert s[0] == c;
  assert s == s[0..0] + [s[0]];
}

lemma Str2IntAppend(s: string, c: char)
  requires ValidBitString(s)
  requires c == '0' || c == '1'
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
  if |s| == 0 {
    assert s + [c] == [c];
    Str2IntSingle(c);
  } else {
    assert (s + [c])[0..|s + [c]| - 1] == s;
    assert (s + [c])[|s + [c]| - 1] == c;
  }
}

lemma AddWithCarryBaseCase(carry: nat)
  requires carry == 0 || carry == 1
  ensures ValidBitString(AddWithCarry("", "", carry))
  ensures Str2Int(AddWithCarry("", "", carry)) == carry
{
  if carry == 0 {
    Str2IntEmpty();
  } else {
    Str2IntSingle('1');
  }
}

lemma AddWithCarryS2Empty(s1: string, carry: nat)
  requires ValidBitString(s1)
  requires carry == 0 || carry == 1
  ensures ValidBitString(AddWithCarry(s1, "", carry))
  ensures Str2Int(AddWithCarry(s1, "", carry)) == Str2Int(s1) + carry
  decreases |s1|
{
  if |s1| == 0 {
    AddWithCarryBaseCase(carry);
  } else if carry == 0 {
    // res == s1
  } else {
    var last := s1[|s1| - 1];
    var rest := s1[0..|s1| - 1];
    
    if last == '0' {
      assert AddWithCarry(s1, "", 1) == rest + ['1'];
      Str2IntAppend(rest, '1');
      assert s1 == rest + [last];
      Str2IntAppend(rest, last);
    } else {
      var recRes := AddWithCarry(rest, "", 1);
      AddWithCarryS2Empty(rest, 1);
      assert AddWithCarry(s1, "", 1) == recRes + ['0'];
      Str2IntAppend(recRes, '0');
      assert s1 == rest + ['1'];
      Str2IntAppend(rest, '1');
    }
  }
}

lemma AddWithCarryS1Empty(s2: string, carry: nat)
  requires ValidBitString(s2)
  requires carry == 0 || carry == 1
  ensures ValidBitString(AddWithCarry("", s2, carry))
  ensures Str2Int(AddWithCarry("", s2, carry)) == Str2Int(s2) + carry
  decreases |s2|
{
  if |s2| == 0 {
    AddWithCarryBaseCase(carry);
  } else if carry == 0 {
    // res == s2
  } else {
    var last := s2[|s2| - 1];
    var rest := s2[0..|s2| - 1];
    
    if last == '0' {
      assert AddWithCarry("", s2, 1) == rest + ['1'];
      Str2IntAppend(rest, '1');
      assert s2 == rest + [last];
      Str2IntAppend(rest, last);
    } else {
      var recRes := AddWithCarry(rest, "", 1);
      AddWithCarryS2Empty(rest, 1);
      assert AddWithCarry("", s2, 1) == recRes + ['0'];
      Str2IntAppend(recRes, '0');
      assert s2 == rest + ['1'];
      Str2IntAppend(rest, '1');
    }
  }
}

lemma AddWithCarryCorrect(s1: string, s2: string, carry: nat)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires carry == 0 || carry == 1
  ensures ValidBitString(AddWithCarry(s1, s2, carry))
  ensures Str2Int(AddWithCarry(s1, s2, carry)) == Str2Int(s1) + Str2Int(s2) + carry
  decreases |s1| + |s2|
{
  var res := AddWithCarry(s1, s2, carry);
  
  if |s1| == 0 && |s2| == 0 {
    AddWithCarryBaseCase(carry);
  } else if |s1| == 0 {
    AddWithCarryS1Empty(s2, carry);
  } else if |s2| == 0 {
    AddWithCarryS2Empty(s1, carry);
  } else {
    var d1 := s1[|s1| - 1];
    var d2 := s2[|s2| - 1];
    var rest1 := s1[0..|s1| - 1];
    var rest2 := s2[0..|s2| - 1];
    
    var sum := (if d1 == '1' then 1 else 0) + (if d2 == '1' then 1 else 0) + carry;
    var newCarry := if sum >= 2 then 1 else 0;
    var digit := if sum % 2 == 1 then '1' else '0';
    
    var recRes := AddWithCarry(rest1, rest2, newCarry);
    AddWithCarryCorrect(rest1, rest2, newCarry);
    
    assert res == recRes + [digit];
    Str2IntAppend(recRes, digit);
    
    assert s1 == rest1 + [d1];
    Str2IntAppend(rest1, d1);
    assert s2 == rest2 + [d2];
    Str2IntAppend(rest2, d2);
    
    assert sum == (if d1 == '1' then 1 else 0) + (if d2 == '1' then 1 else 0) + carry;
    assert newCarry * 2 + (if digit == '1' then 1 else 0) == sum;
  }
}

function AddWithCarry(s1: string, s2: string, carry: nat): string
  requires ValidBitString(s1) && ValidBitString(s2)
  requires carry == 0 || carry == 1
  ensures ValidBitString(AddWithCarry(s1, s2, carry))
  decreases |s1| + |s2|
{
  if |s1| == 0 && |s2| == 0 then
    if carry == 0 then "" else "1"
  else if |s1| == 0 then
    if carry == 0 then s2
    else 
      var last := s2[|s2| - 1];
      var rest := s2[0..|s2| - 1];
      if last == '0' then rest + "1"
      else AddWithCarry(rest, "", 1) + "0"
  else if |s2| == 0 then
    if carry == 0 then s1
    else 
      var last := s1[|s1| - 1];
      var rest := s1[0..|s1| - 1];
      if last == '0' then rest + "1"
      else AddWithCarry(rest, "", 1) + "0"
  else
    var d1 := s1[|s1| - 1];
    var d2 := s2[|s2| - 1];
    var rest1 := s1[0..|s1| - 1];
    var rest2 := s2[0..|s2| - 1];
    var sum := (if d1 == '1' then 1 else 0) + (if d2 == '1' then 1 else 0) + carry;
    var newCarry := if sum >= 2 then 1 else 0;
    var digit := if sum % 2 == 1 then '1' else '0';
    AddWithCarry(rest1, rest2, newCarry) + [digit]
}
// </vc-helpers>

// <vc-spec>
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var result := AddWithCarry(s1, s2, 0);
  AddWithCarryCorrect(s1, s2, 0);
  res := NormalizeBitString(result);
}
// </vc-code>

