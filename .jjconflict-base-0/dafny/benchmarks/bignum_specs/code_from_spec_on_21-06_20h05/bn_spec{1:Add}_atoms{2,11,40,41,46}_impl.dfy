// ATOM BN_46
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// ATOM BN_11
function Exp_int(x: nat, y:nat): nat  
{
  if y == 0 then 1 else x * Exp_int(x, y-1)
}

// ATOM BN_40
function Str2Int(s: string): nat 
  requires ValidBitString(s)
  decreases s
{
      if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

// ATOM BN_31
opaque function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// ATOM BN_41
lemma Str2IntLemma(s: string, i: nat)
requires ValidBitString(s)
requires 0 <= i <= |s|-1
ensures Str2Int(s) == Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..])
{
  assume Str2Int(s) == Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..]);
}

// ATOM : INVARIANT PREDICATE
predicate AddAuxPred(x: string, y: string, oldSb: string, sb: string, oldI: int,
                     oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
{
  ValidBitString(sb) &&
  ValidBitString(x) &&
  ValidBitString(y) &&
  ValidBitString(oldSb) &&
  0 <= carry <= 1 &&
  i <= |x| - 1 && j <= |y| - 1 &&
  oldI <= |x| - 1 && oldJ <= |y| - 1 &&
  i >= -1 &&
  j >= -1 &&
  (oldI >= 0 ==> i == oldI - 1) &&
  (oldJ >= 0 ==> j == oldJ - 1) &&
  (oldI < 0 ==> i == oldI) &&
  (oldJ < 0 ==> j == oldJ) &&
  (oldI >= 0 ==> (bitX == if x[oldI] == '1' then 1 else 0)) &&
  (oldJ >= 0 ==> (bitY == if y[oldJ] == '1' then 1 else 0)) &&
  (oldI < 0 ==> bitX == 0) &&
  (oldJ < 0 ==> bitY == 0) &&
  |oldSb| == |sb| - 1 &&
  sum == bitX + bitY + oldCarry &&
  digit == sum % 2 &&
  carry == sum / 2 &&
  (if digit == 1 then ['1'] + oldSb else ['0'] + oldSb) == sb
}

// ATOM BN_2
lemma AddAuxTop(x: string, y: string, oldSb: string, sb: string, oldI: int,
                oldJ: int, i:int, j:int, carry:nat, bitX:nat, bitY:nat, digit:nat, sum:nat, oldCarry:nat)
  requires AddAuxPred(x, y, oldSb, sb, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry)
  ensures Str2Int(oldSb) +
          (oldCarry * Pow2(|oldSb|)) +
          (if oldI >= 0 then Str2Int(x[0..oldI+1]) * Pow2(|oldSb|) else 0) +
          (if oldJ >= 0 then Str2Int(y[0..oldJ+1]) * Pow2(|oldSb|) else 0) ==
          Str2Int(sb) +
          (carry * Pow2(|sb|)) +
          (if i >= 0 then Str2Int(x[0..i+1]) * Pow2(|sb|) else 0) +
          (if j >= 0 then Str2Int(y[0..j+1]) * Pow2(|sb|) else 0)
{
}

// IMPL BN_1
method Add(s1: string, s2: string) returns (res: string) 
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  /* code modified by LLM (iteration 1): reveal opaque function */
  reveal Pow2();
  
  /* code modified by LLM (iteration 1): handle empty string cases properly */
  if |s1| == 0 && |s2| == 0 {
    res := "";
    return;
  }
  
  if |s1| == 0 {
    res := s2;
    return;
  }
  
  if |s2| == 0 {
    res := s1;
    return;
  }
  
  /* code modified by LLM (iteration 1): main addition algorithm with proper initialization */
  var i := |s1| - 1;
  var j := |s2| - 1;
  var carry := 0;
  res := "";
  
  while i >= 0 || j >= 0 || carry > 0
    invariant i >= -1 && j >= -1
    invariant i < |s1| && j < |s2|
    invariant 0 <= carry <= 1
    invariant ValidBitString(res)
    invariant Str2Int(res) + 
              (carry * Pow2(|res|)) +
              (if i >= 0 then Str2Int(s1[0..i+1]) * Pow2(|res|) else 0) +
              (if j >= 0 then Str2Int(s2[0..j+1]) * Pow2(|res|) else 0) ==
              Str2Int(s1) + Str2Int(s2)
    /* code modified by LLM (iteration 1): fixed decreases clause */
    decreases (if i >= 0 then i + 1 else 0) + (if j >= 0 then j + 1 else 0) + carry
  {
    /* code modified by LLM (iteration 1): save old state for proof */
    var oldRes := res;
    var oldI := i;
    var oldJ := j;
    var oldCarry := carry;
    
    /* code modified by LLM (iteration 1): calculate current bits */
    var bitX := if i >= 0 then (if s1[i] == '1' then 1 else 0) else 0;
    var bitY := if j >= 0 then (if s2[j] == '1' then 1 else 0) else 0;
    var sum := bitX + bitY + carry;
    var digit := sum % 2;
    
    /* code modified by LLM (iteration 1): update result and carry with correct string concatenation */
    var digitStr := if digit == 1 then "1" else "0";
    res := digitStr + res;
    carry := sum / 2;
    
    /* code modified by LLM (iteration 1): update indices */
    if i >= 0 { i := i - 1; }
    if j >= 0 { j := j - 1; }
    
    /* code modified by LLM (iteration 1): establish string representation correspondence */
    assert digitStr == (if digit == 1 then "1" else "0");
    assert digitStr == [if digit == 1 then '1' else '0'];
    assert res == [if digit == 1 then '1' else '0'] + oldRes;
    
    /* code modified by LLM (iteration 1): apply lemma if we have valid old state */
    if oldI >= 0 || oldJ >= 0 || oldCarry > 0 {
      /* code modified by LLM (iteration 1): establish AddAuxPred preconditions */
      assert AddAuxPred(s1, s2, oldRes, res, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
      AddAuxTop(s1, s2, oldRes, res, oldI, oldJ, i, j, carry, bitX, bitY, digit, sum, oldCarry);
    }
  }
}