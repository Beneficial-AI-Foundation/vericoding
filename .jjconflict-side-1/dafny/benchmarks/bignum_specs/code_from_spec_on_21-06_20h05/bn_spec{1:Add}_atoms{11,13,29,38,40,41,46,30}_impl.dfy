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

// ATOM BN_13
lemma Expand(A:nat, B:nat, C:nat) 
  ensures A * (B + 1) * C == A * C + A * B * C
{
}

// ATOM BN_38
lemma Rearrange(A:int, B:int, C:int) 
  ensures (A * 2 + B) * C == A * 2 * C + B * C
{
}

// ATOM BN_30
method NormalizeBitString(s: string) returns(t: string) 
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  t := "";
  assume ValidBitString(t);
  assume |t| > 0;
  assume |t| > 1 ==> t[0] != '0';
  assume ValidBitString(s) ==> Str2Int(s) == Str2Int(t);
}

//IMPL BN_1
//CONSTRAINTS: don't use + on integers and mapping back to strings for computing the final result
method Add(s1: string, s2: string) returns (res: string) 
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  /* code modified by LLM (iteration 2): Handle empty strings with proper bit string results */
  if |s1| == 0 && |s2| == 0 {
    res := "0";
    return;
  }
  
  if |s1| == 0 {
    if |s2| == 0 {
      res := "0";
    } else {
      res := s2;
    }
    return;
  }
  
  if |s2| == 0 {
    res := s1;
    return;
  }
  
  /* code modified by LLM (iteration 2): Use iterative approach for binary addition */
  var result := [];
  var carry := 0;
  var i1 := |s1| - 1;
  var i2 := |s2| - 1;
  
  /* code modified by LLM (iteration 2): Process bits from right to left */
  while i1 >= 0 || i2 >= 0 || carry > 0
    invariant -1 <= i1 < |s1|
    invariant -1 <= i2 < |s2|
    invariant 0 <= carry <= 2
    invariant ValidBitString(result)
  {
    var bit1 := if i1 >= 0 then (if s1[i1] == '1' then 1 else 0) else 0;
    var bit2 := if i2 >= 0 then (if s2[i2] == '1' then 1 else 0) else 0;
    
    var sum := bit1 + bit2 + carry;
    var result_bit := if sum % 2 == 1 then '1' else '0';
    carry := sum / 2;
    
    result := [result_bit] + result;
    
    i1 := i1 - 1;
    i2 := i2 - 1;
  }
  
  /* code modified by LLM (iteration 2): Handle empty result case */
  if |result| == 0 {
    res := "0";
  } else {
    res := result;
  }
}