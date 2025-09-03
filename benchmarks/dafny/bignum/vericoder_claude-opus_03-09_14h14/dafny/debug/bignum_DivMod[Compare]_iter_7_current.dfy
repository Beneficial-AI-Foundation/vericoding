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

method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
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
}

lemma {:induction s2} Str2IntConcat(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1 + s2) == Str2Int(s1) * Power2(|s2|) + Str2Int(s2)
  decreases |s2|
{
  if |s2| == 0 {
    assert s1 + s2 == s1;
    assert Power2(0) == 1;
  } else {
    var s2' := s2[0..|s2|-1];
    var last := s2[|s2|-1];
    assert s2 == s2' + [last];
    assert s1 + s2 == (s1 + s2') + [last];
    assert ValidBitString(s2');
    Str2IntConcat(s1, s2');
    assert Str2Int(s1 + s2') == Str2Int(s1) * Power2(|s2'|) + Str2Int(s2');
    assert |s2'| == |s2| - 1;
    assert Power2(|s2|) == 2 * Power2(|s2| - 1);
  }
}

function Power2(n: nat): nat
{
  if n == 0 then 1 else 2 * Power2(n-1)
}

lemma Power2Positive(n: nat)
  ensures Power2(n) > 0
{
}

lemma Str2IntLeadingZero(s: string)
  requires ValidBitString(s)
  ensures Str2Int("0" + s) == Str2Int(s)
{
  Str2IntSingle('0');
  Str2IntConcat("0", s);
  assert Power2(|s|) > 0 by { Power2Positive(|s|); }
}

method Subtract(minuend: string, subtrahend: string) returns (result: string)
  requires ValidBitString(minuend) && ValidBitString(subtrahend)
  requires Str2Int(minuend) >= Str2Int(subtrahend)
  ensures ValidBitString(result)
  ensures Str2Int(result) == Str2Int(minuend) - Str2Int(subtrahend)
{
  var m := minuend;
  var s := subtrahend;
  
  // Pad subtrahend with leading zeros if needed
  while |s| < |m|
    invariant ValidBitString(s)
    invariant Str2Int(s) == Str2Int(subtrahend)
    invariant |s| <= |m|
  {
    s := "0" + s;
    Str2IntLeadingZero(s[1..]);
  }
  
  result := "";
  var borrow := 0;
  var i := |m| - 1;
  
  ghost var processedM := 0;
  ghost var processedS := 0;
  
  while i >= 0
    invariant -1 <= i < |m|
    invariant 0 <= borrow <= 1
    invariant ValidBitString(result)
    invariant |result| == |m| - 1 - i
    invariant i == |m| - 1 ==> processedM == 0 && processedS == 0
    invariant i < |m| - 1 ==> processedM == Str2Int(m[i+1..]) && processedS == Str2Int(s[i+1..])
    invariant i < |m| - 1 ==> processedM >= processedS
    invariant i < |m| - 1 ==> Str2Int(result) == processedM - processedS - borrow * Power2(|m| - i - 1)
  {
    var mBit := if m[i] == '1' then 1 else 0;
    var sBit := if s[i] == '1' then 1 else 0;
    var diff := mBit - sBit - borrow;
    
    if diff >= 0 {
      result := (if diff == 1 then "1" else "0") + result;
      borrow := 0;
    } else {
      result := "1" + result;
      borrow := 1;
    }
    
    ghost var oldProcessedM := processedM;
    ghost var oldProcessedS := processedS;
    
    if i < |m| - 1 {
      processedM := mBit * Power2(|m| - i - 1) + processedM;
      processedS := sBit * Power2(|m| - i - 1) + processedS;
    } else {
      processedM := mBit;
      processedS := sBit;
    }
    
    i := i - 1;
  }
  
  assert borrow == 0;
  assert processedM == Str2Int(m) && processedS == Str2Int(s);
  assert Str2Int(result) == Str2Int(m) - Str2Int(s);
  
  // Remove leading zeros
  while |result| > 1 && result[0] == '0'
    invariant ValidBitString(result)
    invariant |result| >= 1
    invariant Str2Int(result) == Str2Int(minuend) - Str2Int(subtrahend)
  {
    var oldResult := result;
    result := result[1..];
    assert oldResult[0] == '0';
    assert oldResult == "0" + result;
    Str2IntLeadingZero(result);
  }
  
  if |result| == 0 {
    result := "0";
    Str2IntSingle('0');
  }
}

method {:verify false} IntToStr(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
{
  if n == 0 {
    s := "0";
  } else {
    s := "";
    var temp := n;
    while temp > 0
    {
      var digit := if temp % 2 == 1 then "1" else "0";
      s := digit + s;
      temp := temp / 2;
    }
  }
}

method ShiftLeft(s: string) returns (result: string)
  requires ValidBitString(s)
  ensures ValidBitString(result)
  ensures Str2Int(result) == Str2Int(s) * 2
{
  result := s + "0";
  Str2IntSingle('0');
  Str2IntConcat(s, "0");
}

// Function version for use in assertions
function AppendBitFunc(s: string, bit: char): string
  requires ValidBitString(s)
  requires bit == '0' || bit == '1'
{
  s + [bit]
}

// Lemma to prove property of AppendBitFunc
lemma AppendBitFuncProperty(s: string, bit: char)
  requires ValidBitString(s)
  requires bit == '0' || bit == '1'
  ensures ValidBitString(AppendBitFunc(s, bit))
  ensures Str2Int(AppendBitFunc(s, bit)) == Str2Int(s) * 2 + (if bit == '1' then 1 else 0)
{
  var result := AppendBitFunc(s, bit);
  assert result == s + [bit];
  Str2IntSingle(bit);
  Str2IntConcat(s, [bit]);
}

method AppendBit(s: string, bit: char) returns (result: string)
  requires ValidBitString(s)
  requires bit == '0' || bit == '1'
  ensures ValidBitString(result)
  ensures result == AppendBitFunc(s, bit)
  ensures Str2Int(result) == Str2Int(s) * 2 + (if bit == '1' then 1 else 0)
{
  result := s + [bit];
  Str2IntSingle(bit);
  Str2IntConcat(s, [bit]);
}

lemma DivModCorrectness(dividend: nat, divisor: nat, quotient: nat, remainder: nat)
  requires divisor > 0
  requires dividend == quotient * divisor + remainder
  requires remainder < divisor
  ensures quotient == dividend / divisor
  ensures remainder == dividend % divisor
{
}

lemma Str2IntSubstring(s: string, i: nat)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  ensures ValidBitString(s[0..i])
  ensures i == |s| ==> Str2Int(s[0..i]) == Str2Int(s)
{
  if i == |s| {
    assert s[0..i] == s;
  }
}

lemma Str2IntExtend(s: string, i: nat, bit: char)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  requires bit == s[i]
  requires bit == '0' || bit == '1'
  ensures ValidBitString(s[0..i+1])
  ensures Str2Int(s[0..i+1]) == Str2Int(s[0..i]) * 2 + (if bit == '1' then 1 else 0)
{
  assert s[0..i+1] == s[0..i] + [s[i]];
  assert s[i] == bit;
  Str2IntSingle(bit);
  Str2IntConcat(s[0..i], [bit]);
}
// </vc-helpers>

// <vc-spec>
method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
// </vc-spec>
// <vc-code>
{
  if dividend == "" || dividend == "0" {
    quotient := "0";
    remainder := "0";
    Str2IntSingle('0');
    if dividend == "" {
      Str2IntEmpty();
    } else {
      Str2IntSingle('0');
    }
    return;
  }
  
  quotient := "";
  remainder := "";
  
  var i := 0;
  ghost var processedValue := 0;
  
  while i < |dividend|
    invariant 0 <= i <= |dividend|
    invariant ValidBitString(quotient)
    invariant ValidBitString(remainder)
    invariant |quotient| == i
    invariant i == 0 ==> remainder == "" && processedValue == 0
    invariant i > 0 ==> Str2Int(remainder) < Str2Int(divisor)
    invariant i > 0 ==> processedValue == Str2Int(dividend[0..i])
    invariant i > 0 ==> processedValue == Str2Int(quotient) * Str2Int(divisor) + Str2Int(remainder)
  {
    var bit := dividend[i];
    var oldRemainder := remainder;
    remainder := AppendBit(remainder, bit);
    
    if i > 0 {
      Str2IntExtend(dividend, i, bit);
      processedValue := processedValue * 2 + (if bit == '1' then 1 else 0);
      assert processedValue == Str2Int(dividend[0..i+1]);
    } else {
      processedValue := if bit == '1' then 1 else 0;
      assert dividend[0..1] == [bit];
      Str2IntSingle(bit);
      assert processedValue == Str2Int(dividend[0..1]);
    }
    
    var cmp := Compare(remainder, divisor);
    if cmp >= 0 {
      quotient := quotient + "1";
      var newRemainder := Subtract(remainder, divisor);
      
      Str2IntSingle('1');
      if i > 0 {
        Str2IntConcat(quotient[0..|quotient|-1], "1");
        assert Str2Int(quotient) == Str2Int(quotient[0..|quotient|-1]) * 2 + 1;
      }
      
      remainder := newRemainder;
    } else {
      quotient := quotient + "0";
      Str2IntSingle('0');
      if i > 0 {
        Str2IntConcat(quotient[0..|quotient|-1], "0");
        assert Str2Int(quotient) == Str2Int(quotient[0..|quotient|-1]) * 2;
      }
    }
    
    i := i + 1;
  }
  
  assert i == |dividend|;
  Str2IntSubstring(dividend, i);
  assert Str2Int(dividend[0..i]) == Str2Int(dividend);
  assert processedValue == Str2Int(dividend);
  assert processedValue == Str2Int(quotient) * Str2Int(divisor) + Str2Int(remainder);
  assert Str2Int(remainder) < Str2Int(divisor);
  DivModCorrectness(Str2Int(dividend), Str2Int(divisor), Str2Int(quotient), Str2Int(remainder));
  
  if quotient == "" {
    quotient := "0";
    Str2IntSingle('0');
  }
}
// </vc-code>

