

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

// ATOM BN_41
lemma Str2IntLemma(s: string, i: nat)
requires ValidBitString(s)
requires 0 <= i <= |s|-1
ensures Str2Int(s) == Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..])
{
  assume Str2Int(s) == Str2Int(s[..i+1]) * Exp_int(2, |s|-1 - i) + Str2Int(s[i+1..]);
}

// ATOM BN_29
lemma MulIsAssociative(a: nat, b: nat, c: nat) 
  ensures a * (b * c) == a * b * c
{
}

// SPEC BN_27
//CONSTRAINTS: don't use * on integers and mapping back to strings for computing the final result
method Mul(s1: string, s2: string) returns (res: string) 
requires ValidBitString(s1) && ValidBitString(s2)
ensures ValidBitString(res)
ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{}

