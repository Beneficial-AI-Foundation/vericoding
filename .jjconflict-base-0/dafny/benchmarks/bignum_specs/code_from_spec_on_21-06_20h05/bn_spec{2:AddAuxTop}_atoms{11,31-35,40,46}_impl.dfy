// ATOM BN_11
predicate ValidBitString(s: string) 
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// ATOM BN_46
function Exp_int(x: nat, y:nat): nat 
{
  if y == 0 then 1 else x * Exp_int(x, y-1)
}

// ATOM BN_31
opaque function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// ATOM BN_32
lemma Pow2Inductive(i: nat)
  ensures Pow2(i+1) == 2*Pow2(i)
{
  reveal Pow2();
}

// ATOM BN_33
lemma Pow2Monotonic(a: nat, b:nat)
  requires a <= b
  ensures Pow2(a) <= Pow2(b)
{
  reveal Pow2;
}

// ATOM BN_34
lemma Pow2Positive(n:nat)
  ensures Pow2(n) > 0
{
  if n == 0 {
    Pow2Zero();
  }
  else {
    Pow2Positive(n-1);
    reveal Pow2();
  }
}

// ATOM BN_35
lemma Pow2Zero()
  ensures Pow2(0) == 1
{
  reveal Pow2();
}

// ATOM BN_40
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
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

// IMPL 2
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
  // From the predicate, we know that sb is constructed by prepending a digit to oldSb
  // and |sb| == |oldSb| + 1, so Pow2(|sb|) == 2 * Pow2(|oldSb|)
  Pow2Inductive(|oldSb|);
  
  // We know that sb = [digit_char] + oldSb where digit_char is '1' or '0' based on digit
  // So Str2Int(sb) = 2 * Str2Int(oldSb) + digit
  
  // From the predicate: sum = bitX + bitY + oldCarry, digit = sum % 2, carry = sum / 2
  // So sum = 2 * carry + digit
  
  // The key insight is that when we move from oldI to i and oldJ to j,
  // we're essentially "consuming" the bits at positions oldI and oldJ
  // and incorporating them into the sum calculation
  
  // We need to show that the invariant holds by arithmetic manipulation
  // using the relationships from the predicate
}