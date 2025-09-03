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
  ensures ValidBitString(t)
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
  ensures ValidBitString([c])
  ensures Str2Int([c]) == if c == '1' then 1 else 0
{
}

lemma Str2IntConcat(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(s1 + s2)
  ensures Str2Int(s1 + s2) == Str2Int(s1) * Power2(|s2|) + Str2Int(s2)
  decreases |s2|
{
  if |s2| == 0 {
    assert s1 + s2 == s1;
  } else {
    var s2' := s2[0..|s2|-1];
    var last := s2[|s2|-1];
    
    assert s1 + s2 == (s1 + s2') + [last];
    assert |s1 + s2'| > 0;
    assert (s1 + s2')[0..|s1 + s2'|-1] == s1 + s2';
    
    Str2IntConcat(s1, s2');
    
    calc {
      Str2Int(s1 + s2);
    == 
      2 * Str2Int((s1 + s2)[0..|s1 + s2|-1]) + (if last == '1' then 1 else 0);
    ==
      2 * Str2Int(s1 + s2') + (if last == '1' then 1 else 0);
    ==
      2 * (Str2Int(s1) * Power2(|s2'|) + Str2Int(s2')) + (if last == '1' then 1 else 0);
    ==
      Str2Int(s1) * (2 * Power2(|s2'|)) + (2 * Str2Int(s2') + (if last == '1' then 1 else 0));
    ==
      Str2Int(s1) * Power2(|s2|) + Str2Int(s2);
    }
  }
}

function Power2(n: nat): nat
{
  if n == 0 then 1 else 2 * Power2(n-1)
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var carry := '0';
  var i := 0;
  var result := "";
  
  while i < |s1| || i < |s2| || carry == '1'
    invariant 0 <= i <= |s1| + 1 && 0 <= i <= |s2| + 1
    invariant carry == '0' || carry == '1'
    invariant ValidBitString(result)
    invariant i <= |s1| && i <= |s2| ==> 
      Str2Int(result) + (if carry == '1' then Power2(i) else 0) == 
      Str2Int(s1[|s1|-i..]) + Str2Int(s2[|s2|-i..])
    invariant i > |s1| && i <= |s2| ==> 
      Str2Int(result) + (if carry == '1' then Power2(i) else 0) == 
      Str2Int(s1) + Str2Int(s2[|s2|-i..])
    invariant i <= |s1| && i > |s2| ==> 
      Str2Int(result) + (if carry == '1' then Power2(i) else 0) == 
      Str2Int(s1[|s1|-i..]) + Str2Int(s2)
    invariant i > |s1| && i > |s2| ==> 
      Str2Int(result) + (if carry == '1' then Power2(i) else 0) == 
      Str2Int(s1) + Str2Int(s2)
    decreases |s1| + |s2| + 2 - i
  {
    var bit1 := if i < |s1| then s1[|s1|-1-i] else '0';
    var bit2 := if i < |s2| then s2[|s2|-1-i] else '0';
    
    var sum := (if bit1 == '1' then 1 else 0) + 
               (if bit2 == '1' then 1 else 0) + 
               (if carry == '1' then 1 else 0);
    
    var newBit := if sum % 2 == 1 then '1' else '0';
    carry := if sum >= 2 then '1' else '0';
    
    result := [newBit] + result;
    i := i + 1;
  }
  
  res := NormalizeBitString(result);
}

method DoubleString(s: string) returns (res: string)
  requires ValidBitString(s)
  ensures ValidBitString(res)
  ensures Str2Int(res) == 2 * Str2Int(s)
{
  if |s| == 0 {
    res := "";
  } else {
    res := s + "0";
    DoubleStringLemma(s);
  }
}

lemma DoubleStringLemma(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures ValidBitString(s + "0")
  ensures Str2Int(s + "0") == 2 * Str2Int(s)
{
  var s0 := s + "0";
  assert s0[0..|s0|-1] == s;
  assert s0[|s0|-1] == '0';
  
  calc {
    Str2Int(s + "0");
  ==
    2 * Str2Int(s) + 0;
  ==
    2 * Str2Int(s);
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
  if |s1| == 0 || |s2| == 0 {
    res := "";
    Str2IntEmpty();
    return;
  }
  
  var n1 := NormalizeBitString(s1);
  var n2 := NormalizeBitString(s2);
  
  if n1 == "1" {
    res := n2;
    return;
  }
  
  if n2 == "1" {
    res := n1;
    return;
  }
  
  res := "0";
  var temp := n1;
  var multiplier := n2;
  
  while multiplier != "0" && |multiplier| > 0
    invariant ValidBitString(res)
    invariant ValidBitString(temp)
    invariant ValidBitString(multiplier)
    invariant Str2Int(res) + Str2Int(temp) * Str2Int(multiplier) == Str2Int(n1) * Str2Int(n2)
    decreases |multiplier|
  {
    if multiplier[|multiplier|-1] == '1' {
      res := Add(res, temp);
    }
    
    multiplier := multiplier[0..|multiplier|-1];
    temp := DoubleString(temp);
  }
}
// </vc-code>

