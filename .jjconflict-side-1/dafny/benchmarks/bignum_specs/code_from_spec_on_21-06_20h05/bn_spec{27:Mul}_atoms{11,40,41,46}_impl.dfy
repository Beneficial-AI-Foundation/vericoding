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

/* code modified by LLM (iteration 1): Fixed BinaryAdd with proper implementation and verification */
method BinaryAdd(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  if |s1| == 0 { res := s2; return; }
  if |s2| == 0 { res := s1; return; }
  
  var maxLen := if |s1| > |s2| then |s1| else |s2|;
  var result := "";
  var carry := 0;
  
  var i := 0;
  while i < maxLen || carry > 0
    invariant 0 <= i
    invariant ValidBitString(result)
    invariant 0 <= carry <= 1
    decreases maxLen + 2 - i
  {
    var bit1 := 0;
    var bit2 := 0;
    
    if i < |s1| {
      var idx1 := |s1| - 1 - i;
      bit1 := if s1[idx1] == '1' then 1 else 0;
    }
    
    if i < |s2| {
      var idx2 := |s2| - 1 - i;
      bit2 := if s2[idx2] == '1' then 1 else 0;
    }
    
    var sum := bit1 + bit2 + carry;
    var resultBit := sum % 2;
    carry := sum / 2;
    
    result := (if resultBit == 1 then "1" else "0") + result;
    
    i := i + 1;
  }
  
  res := result;
}

/* code modified by LLM (iteration 1): Added helper lemma for string concatenation with zero */
lemma AppendZeroLemma(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(s + "0")
  ensures Str2Int(s + "0") == 2 * Str2Int(s)
{
  var newS := s + "0";
  if |s| == 0 {
    assert newS == "0";
    assert Str2Int(newS) == 0;
    assert Str2Int(s) == 0;
  } else {
    assert newS[|newS|-1] == '0';
    assert newS[0..|newS|-1] == s;
    assert Str2Int(newS) == 2 * Str2Int(s) + 0;
  }
}

/* code modified by LLM (iteration 1): Fixed AppendZeros method */
method AppendZeros(s: string, count: nat) returns (result: string)
  requires ValidBitString(s)
  ensures ValidBitString(result)
  ensures |result| == |s| + count
  ensures Str2Int(result) == Str2Int(s) * Exp_int(2, count)
{
  result := s;
  var i := 0;
  while i < count
    invariant 0 <= i <= count
    invariant ValidBitString(result)
    invariant |result| == |s| + i
    invariant Str2Int(result) == Str2Int(s) * Exp_int(2, i)
    decreases count - i
  {
    AppendZeroLemma(result);
    result := result + "0";
    i := i + 1;
  }
}

// IMPL BN_27
//CONSTRAINTS: don't use * on integers and mapping back to strings for computing the final result
/* code modified by LLM (iteration 1): Complete rewrite of Mul method with proper verification */
method Mul(s1: string, s2: string) returns (res: string) 
requires ValidBitString(s1) && ValidBitString(s2)
ensures ValidBitString(res)
ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  // Handle edge cases
  if |s1| == 0 || |s2| == 0 {
    res := "0";
    return;
  }
  
  // Check for zero strings
  var s1IsZero := true;
  var k := 0;
  while k < |s1|
    invariant 0 <= k <= |s1|
    invariant s1IsZero == forall j | 0 <= j < k :: s1[j] == '0'
    decreases |s1| - k
  {
    if s1[k] == '1' {
      s1IsZero := false;
      break;
    }
    k := k + 1;
  }
  
  var s2IsZero := true;
  k := 0;
  while k < |s2|
    invariant 0 <= k <= |s2|
    invariant s2IsZero == forall j | 0 <= j < k :: s2[j] == '0'
    decreases |s2| - k
  {
    if s2[k] == '1' {
      s2IsZero := false;
      break;
    }
    k := k + 1;
  }
  
  if s1IsZero || s2IsZero {
    res := "0";
    return;
  }
  
  // Binary multiplication using shift and add
  res := "0";
  var i := 0;
  
  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant ValidBitString(res)
    decreases |s2| - i
  {
    var bitPos := |s2| - 1 - i;
    
    if s2[bitPos] == '1' {
      var shifted := AppendZeros(s1, i);
      res := BinaryAdd(res, shifted);
    }
    
    i := i + 1;
  }
}