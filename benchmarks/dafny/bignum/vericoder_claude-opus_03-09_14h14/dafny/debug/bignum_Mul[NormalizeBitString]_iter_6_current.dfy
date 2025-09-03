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
    assert Power2(0) == 1;
  } else {
    var s2' := s2[0..|s2|-1];
    var last := s2[|s2|-1];
    
    assert s1 + s2 == (s1 + s2') + [last];
    assert ValidBitString(s2');
    assert ValidBitString([last]);
    
    Str2IntConcat(s1, s2');
    
    assert (s1 + s2)[0..|s1 + s2|-1] == s1 + s2';
    assert Str2Int(s2) == 2 * Str2Int(s2') + (if last == '1' then 1 else 0);
    assert Power2(|s2|) == 2 * Power2(|s2'|);
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
    invariant 0 <= i <= max(|s1|, |s2|) + 1
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
    decreases max(|s1|, |s2|) + 2 - i
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

function max(a: nat, b: nat): nat
{
  if a >= b then a else b
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
}

lemma MulByPower2(s: string, n: nat)
  requires ValidBitString(s)
  ensures ValidBitString(s + Zeros(n))
  ensures Str2Int(s + Zeros(n)) == Str2Int(s) * Power2(n)
  decreases n
{
  if n == 0 {
    assert Zeros(0) == "";
    assert s + "" == s;
    assert Power2(0) == 1;
  } else {
    var zn1 := Zeros(n-1);
    assert Zeros(n) == zn1 + "0";
    MulByPower2(s, n-1);
    assert s + Zeros(n) == (s + zn1) + "0";
    DoubleStringLemma(s + zn1);
    assert Power2(n) == 2 * Power2(n-1);
  }
}

function Zeros(n: nat): string
  ensures ValidBitString(Zeros(n))
  ensures |Zeros(n)| == n
  ensures Str2Int(Zeros(n)) == 0
  decreases n
{
  if n == 0 then 
    ""
  else 
    var z := Zeros(n-1);
    assert Str2Int("0" + z) == 2 * Str2Int(z) + 0 == 0;
    "0" + z
}

lemma MulStepCorrect(s1: string, s2: string, i: nat, res: string)
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(res)
  requires 0 < i <= |s2|
  requires Str2Int(res) == Str2Int(s1) * Str2Int(s2[i..])
  ensures s2[i-1..][0..|s2[i-1..]|-1] == s2[i..]
  ensures Str2Int(s2[i-1..]) == 2 * Str2Int(s2[i..]) + (if s2[i-1] == '1' then 1 else 0)
{
  assert s2[i-1..] == [s2[i-1]] + s2[i..];
  assert s2[i-1..][0..|s2[i-1..]|-1] == s2[i..];
}

lemma MulLoopInvariant(s1: string, s2: string, i: nat, res: string)
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(res)
  requires 0 < i <= |s2|
  requires Str2Int(res) == Str2Int(s1) * Str2Int(s2[i..])
  ensures ValidBitString(DoubleString(res))
  ensures s2[i-1] == '0' ==> Str2Int(DoubleString(res)) == Str2Int(s1) * Str2Int(s2[i-1..])
  ensures s2[i-1] == '1' ==> ValidBitString(Add(DoubleString(res), s1)) && Str2Int(Add(DoubleString(res), s1)) == Str2Int(s1) * Str2Int(s2[i-1..])
{
  MulStepCorrect(s1, s2, i, res);
  var doubled := DoubleString(res);
  assert Str2Int(doubled) == 2 * Str2Int(res);
  assert Str2Int(doubled) == 2 * (Str2Int(s1) * Str2Int(s2[i..]));
  
  if s2[i-1] == '0' {
    assert Str2Int(s2[i-1..]) == 2 * Str2Int(s2[i..]);
    assert Str2Int(doubled) == Str2Int(s1) * Str2Int(s2[i-1..]);
  } else {
    assert s2[i-1] == '1';
    assert Str2Int(s2[i-1..]) == 2 * Str2Int(s2[i..]) + 1;
    var added := Add(doubled, s1);
    assert Str2Int(added) == Str2Int(doubled) + Str2Int(s1);
    assert Str2Int(added) == 2 * (Str2Int(s1) * Str2Int(s2[i..])) + Str2Int(s1);
    assert Str2Int(added) == Str2Int(s1) * (2 * Str2Int(s2[i..]) + 1);
    assert Str2Int(added) == Str2Int(s1) * Str2Int(s2[i-1..]);
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
  res := "0";
  var i := |s2|;
  
  assert s2[|s2|..] == "";
  assert Str2Int("") == 0;
  assert Str2Int(res) == Str2Int(s1) * Str2Int(s2[i..]);
  
  while i > 0
    invariant 0 <= i <= |s2|
    invariant ValidBitString(res)
    invariant Str2Int(res) == Str2Int(s1) * Str2Int(s2[i..])
    decreases i
  {
    MulLoopInvariant(s1, s2, i, res);
    res := DoubleString(res);
    if s2[i-1] == '1' {
      res := Add(res, s1);
    }
    i := i - 1;
  }
  
  assert i == 0;
  assert s2[0..] == s2;
}
// </vc-code>

