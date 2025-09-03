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

// <vc-helpers>
lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{
}

lemma Str2IntAppend(s: string, c: char)
  requires ValidBitString(s)
  requires c == '0' || c == '1'
  ensures ValidBitString(s + [c])
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
  assert ValidBitString(s + [c]);
  if |s| == 0 {
    assert s + [c] == [c];
    calc {
      Str2Int(s + [c]);
      == Str2Int([c]);
      == 2 * Str2Int("") + (if c == '1' then 1 else 0);
      == 2 * 0 + (if c == '1' then 1 else 0);
      == (if c == '1' then 1 else 0);
      == 2 * Str2Int(s) + (if c == '1' then 1 else 0);
    }
  } else {
    assert (s + [c])[0..|s + [c]|-1] == s;
    assert (s + [c])[|s + [c]|-1] == c;
  }
}

lemma AddWithCarryCorrect(s1: string, s2: string, carry: nat)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires carry == 0 || carry == 1
  ensures ValidBitString(AddWithCarry(s1, s2, carry))
  ensures Str2Int(AddWithCarry(s1, s2, carry)) == Str2Int(s1) + Str2Int(s2) + carry
{
  var res := AddWithCarry(s1, s2, carry);
  
  if |s1| == 0 && |s2| == 0 {
    if carry == 0 {
      assert res == "";
      Str2IntEmpty();
    } else {
      assert res == "1";
    }
  } else if |s1| == 0 {
    if carry == 0 {
      assert res == s2;
    } else {
      AddOneCorrect(s2);
    }
  } else if |s2| == 0 {
    if carry == 0 {
      assert res == s1;
    } else {
      AddOneCorrect(s1);
    }
  } else {
    var bit1 := if s1[|s1|-1] == '1' then 1 else 0;
    var bit2 := if s2[|s2|-1] == '1' then 1 else 0;
    var sum := bit1 + bit2 + carry;
    var newBit := if sum % 2 == 1 then '1' else '0';
    var newCarry := sum / 2;
    
    var s1Prefix := s1[0..|s1|-1];
    var s2Prefix := s2[0..|s2|-1];
    
    assert ValidBitString(s1Prefix) && ValidBitString(s2Prefix);
    
    AddWithCarryCorrect(s1Prefix, s2Prefix, newCarry);
    var recResult := AddWithCarry(s1Prefix, s2Prefix, newCarry);
    
    assert res == recResult + [newBit];
    
    Str2IntAppend(recResult, newBit);
    
    calc {
      Str2Int(res);
      == Str2Int(recResult + [newBit]);
      == 2 * Str2Int(recResult) + (if newBit == '1' then 1 else 0);
      == 2 * (Str2Int(s1Prefix) + Str2Int(s2Prefix) + newCarry) + (if newBit == '1' then 1 else 0);
      == 2 * Str2Int(s1Prefix) + 2 * Str2Int(s2Prefix) + 2 * newCarry + (if newBit == '1' then 1 else 0);
      == { assert Str2Int(s1) == 2 * Str2Int(s1Prefix) + bit1; }
         (Str2Int(s1) - bit1) + 2 * Str2Int(s2Prefix) + 2 * newCarry + (if newBit == '1' then 1 else 0);
      == { assert Str2Int(s2) == 2 * Str2Int(s2Prefix) + bit2; }
         (Str2Int(s1) - bit1) + (Str2Int(s2) - bit2) + 2 * newCarry + (if newBit == '1' then 1 else 0);
      == Str2Int(s1) + Str2Int(s2) - bit1 - bit2 + 2 * newCarry + (if newBit == '1' then 1 else 0);
      == { assert sum == bit1 + bit2 + carry; 
           assert newCarry == sum / 2;
           assert (if newBit == '1' then 1 else 0) == sum % 2;
           assert sum == 2 * newCarry + sum % 2; }
         Str2Int(s1) + Str2Int(s2) - bit1 - bit2 + sum - sum % 2 + sum % 2;
      == Str2Int(s1) + Str2Int(s2) - bit1 - bit2 + sum;
      == Str2Int(s1) + Str2Int(s2) - bit1 - bit2 + bit1 + bit2 + carry;
      == Str2Int(s1) + Str2Int(s2) + carry;
    }
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
    if carry == 0 then s2 else AddOne(s2)
  else if |s2| == 0 then
    if carry == 0 then s1 else AddOne(s1)
  else
    var bit1 := if s1[|s1|-1] == '1' then 1 else 0;
    var bit2 := if s2[|s2|-1] == '1' then 1 else 0;
    var sum := bit1 + bit2 + carry;
    var newBit := if sum % 2 == 1 then '1' else '0';
    var newCarry := sum / 2;
    AddWithCarry(s1[0..|s1|-1], s2[0..|s2|-1], newCarry) + [newBit]
}

function AddOne(s: string): string
  requires ValidBitString(s)
  ensures ValidBitString(AddOne(s))
  decreases |s|
{
  if |s| == 0 then
    "1"
  else if s[|s|-1] == '0' then
    s[0..|s|-1] + ['1']
  else
    AddOne(s[0..|s|-1]) + ['0']
}

lemma AddOneCorrect(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(AddOne(s))
  ensures Str2Int(AddOne(s)) == Str2Int(s) + 1
{
  if |s| == 0 {
    assert AddOne(s) == "1";
    assert Str2Int("1") == 1;
    Str2IntEmpty();
  } else if s[|s|-1] == '0' {
    var res := s[0..|s|-1] + ['1'];
    assert AddOne(s) == res;
    Str2IntAppend(s[0..|s|-1], '1');
    calc {
      Str2Int(res);
      == 2 * Str2Int(s[0..|s|-1]) + 1;
      == { assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 0; }
         Str2Int(s) + 1;
    }
  } else {
    assert s[|s|-1] == '1';
    var prefix := s[0..|s|-1];
    AddOneCorrect(prefix);
    var res := AddOne(prefix) + ['0'];
    assert AddOne(s) == res;
    Str2IntAppend(AddOne(prefix), '0');
    calc {
      Str2Int(res);
      == 2 * Str2Int(AddOne(prefix)) + 0;
      == 2 * (Str2Int(prefix) + 1);
      == 2 * Str2Int(prefix) + 2;
      == { assert Str2Int(s) == 2 * Str2Int(prefix) + 1; }
         Str2Int(s) - 1 + 2;
      == Str2Int(s) + 1;
    }
  }
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
  AddWithCarryCorrect(s1, s2, 0);
  res := AddWithCarry(s1, s2, 0);
}
// </vc-code>

