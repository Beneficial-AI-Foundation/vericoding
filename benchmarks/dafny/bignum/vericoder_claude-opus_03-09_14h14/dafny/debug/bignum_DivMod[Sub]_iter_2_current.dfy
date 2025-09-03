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

method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{
}

lemma Str2IntSingleZero()
  ensures Str2Int("0") == 0
{
}

lemma Str2IntSingleOne()
  ensures Str2Int("1") == 1
{
}

lemma Str2IntAppend(s: string, c: char)
  requires ValidBitString(s)
  requires c == '0' || c == '1'
  ensures ValidBitString(s + [c])
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
  if |s| == 0 {
    assert s + [c] == [c];
    calc {
      Str2Int([c]);
      == (2 * Str2Int([]) + (if c == '1' then 1 else 0));
      == (2 * 0 + (if c == '1' then 1 else 0));
      == (if c == '1' then 1 else 0);
    }
  } else {
    var s' := s + [c];
    assert s'[0..|s'|-1] == s;
    assert s'[|s'|-1] == c;
  }
}

lemma ValidBitStringConcat(s1: string, s2: string)
  requires ValidBitString(s1)
  requires ValidBitString(s2)
  ensures ValidBitString(s1 + s2)
{
}

method CompareStrings(s1: string, s2: string) returns (cmp: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures cmp == 0 ==> Str2Int(s1) == Str2Int(s2)
  ensures cmp > 0 ==> Str2Int(s1) > Str2Int(s2)
  ensures cmp < 0 ==> Str2Int(s1) < Str2Int(s2)
{
  // Remove leading zeros from s1
  var i1 := 0;
  while i1 < |s1| && s1[i1] == '0'
    invariant 0 <= i1 <= |s1|
    invariant forall k | 0 <= k < i1 :: s1[k] == '0'
  {
    i1 := i1 + 1;
  }
  var t1 := if i1 == |s1| then "0" else s1[i1..];
  
  // Remove leading zeros from s2
  var i2 := 0;
  while i2 < |s2| && s2[i2] == '0'
    invariant 0 <= i2 <= |s2|
    invariant forall k | 0 <= k < i2 :: s2[k] == '0'
  {
    i2 := i2 + 1;
  }
  var t2 := if i2 == |s2| then "0" else s2[i2..];
  
  // Compare lengths first
  if |t1| < |t2| {
    cmp := -1;
  } else if |t1| > |t2| {
    cmp := 1;
  } else {
    // Same length, compare lexicographically
    var j := 0;
    cmp := 0;
    while j < |t1| && cmp == 0
      invariant 0 <= j <= |t1|
      invariant |t1| == |t2|
      invariant cmp == 0 ==> forall k | 0 <= k < j :: t1[k] == t2[k]
    {
      if t1[j] < t2[j] {
        cmp := -1;
      } else if t1[j] > t2[j] {
        cmp := 1;
      }
      j := j + 1;
    }
  }
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
  quotient := "";
  remainder := "";
  
  var i := 0;
  while i < |dividend|
    invariant 0 <= i <= |dividend|
    invariant ValidBitString(quotient)
    invariant ValidBitString(remainder)
    invariant Str2Int(dividend[..i]) == Str2Int(quotient) * Str2Int(divisor) + Str2Int(remainder)
    invariant Str2Int(remainder) < Str2Int(divisor)
  {
    var bit := dividend[i];
    Str2IntAppend(remainder, bit);
    remainder := remainder + [bit];
    
    assert dividend[..i+1] == dividend[..i] + [bit];
    Str2IntAppend(dividend[..i], bit);
    
    var cmp := CompareStrings(remainder, divisor);
    if cmp >= 0 {
      remainder := Sub(remainder, divisor);
      Str2IntAppend(quotient, '1');
      quotient := quotient + ['1'];
      
      assert Str2Int(dividend[..i+1]) == 2 * Str2Int(dividend[..i]) + (if bit == '1' then 1 else 0);
      assert Str2Int(dividend[..i+1]) == Str2Int(quotient[..|quotient|-1]) * Str2Int(divisor) * 2 + Str2Int(remainder) + Str2Int(divisor) + (if bit == '1' then 1 else 0);
    } else {
      Str2IntAppend(quotient, '0');
      quotient := quotient + ['0'];
    }
    
    i := i + 1;
  }
  
  assert dividend[..|dividend|] == dividend;
  
  if quotient == "" {
    quotient := "0";
    Str2IntSingleZero();
  }
  
  if remainder == "" {
    remainder := "0";
    Str2IntSingleZero();
  }
}
// </vc-code>

