//ATOM ValidBitString

predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

//ATOM Str2Int

// ----------------------------------------------------
// Str2Int: bit-string -> nat (reference function)
// ----------------------------------------------------
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

//ATOM OStr2Int

// Make an opaque version to speed up verification
opaque function OStr2Int(s: string): nat
  requires ValidBitString(s)
{
  Str2Int(s)
}

//ATOM NormalizeBitString

method NormalizeBitString(s: string) returns(t: string)
  // Remove leading zeros, except keep at least one digit
  ensures ValidBitString(t)
  // I added and proved some extra post-conditions:
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
    t := "";
    assume ValidBitString(t);
    assume |t| > 0;
    assume |t| > 1 ==> t[0] != '0';
    assume ValidBitString(s) ==> Str2Int(s) == Str2Int(t);
    return t;
}

//ATOM Add

// ----------------------------------------------------
// string-based addition (no Str2Int / Int2Str)
// ----------------------------------------------------
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
    res := "";
    assume ValidBitString(res);
    assume Str2Int(res) == Str2Int(s1) + Str2Int(s2);
    return res;
}

//IMPL Mul

/* code modified by LLM (iteration 1): Added helper function for generating zeros */
function Zeros(n: nat): string
  ensures ValidBitString(Zeros(n))
  ensures |Zeros(n)| == n
  ensures forall i | 0 <= i < n :: Zeros(n)[i] == '0'
  ensures Str2Int(Zeros(n)) == 0
  decreases n
{
  if n == 0 then "" else Zeros(n-1) + "0"
}

/* code modified by LLM (iteration 1): Added power of 2 function */
function Pow2(n: nat): nat
  ensures Pow2(n) > 0
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n-1)
}

/* code modified by LLM (iteration 1): Added lemma for zeros string value */
lemma ZerosValue(n: nat)
  ensures Str2Int(Zeros(n)) == 0
  decreases n
{
  if n == 0 {
    // Base case: empty string has value 0
  } else {
    // Inductive case
    ZerosValue(n-1);
    // Str2Int(Zeros(n)) = Str2Int(Zeros(n-1) + "0")
    // = 2 * Str2Int(Zeros(n-1)) + 0 = 2 * 0 + 0 = 0
  }
}

/* code modified by LLM (iteration 1): Added lemma for string concatenation with zeros */
lemma ConcatZerosLemma(s: string, n: nat)
  requires ValidBitString(s)
  ensures ValidBitString(s + Zeros(n))
  ensures Str2Int(s + Zeros(n)) == Str2Int(s) * Pow2(n)
  decreases n
{
  ZerosValue(n);
  if n == 0 {
    assert s + Zeros(0) == s + "" == s;
    assert Pow2(0) == 1;
  } else {
    ConcatZerosLemma(s, n-1);
    var temp := s + Zeros(n-1);
    assert Str2Int(temp) == Str2Int(s) * Pow2(n-1);
    assert Str2Int(temp + "0") == 2 * Str2Int(temp) + 0 == 2 * Str2Int(s) * Pow2(n-1);
    assert 2 * Pow2(n-1) == Pow2(n);
  }
}

/* code modified by LLM (iteration 1): Added partial sum function for mathematical reasoning */
function PartialSum(s1: string, s2: string, k: nat): nat
  requires ValidBitString(s1) && ValidBitString(s2)
  requires k <= |s2|
  decreases k
{
  if k == 0 then 0
  else 
    var bitIndex := |s2| - k;
    var contribution := if s2[bitIndex] == '1' then Str2Int(s1) * Pow2(k-1) else 0;
    PartialSum(s1, s2, k-1) + contribution
}

/* code modified by LLM (iteration 1): Added lemma proving partial sum equals full multiplication */
lemma PartialSumLemma(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures PartialSum(s1, s2, |s2|) == Str2Int(s1) * Str2Int(s2)
  decreases |s2|
{
  if |s2| == 0 {
    assert Str2Int(s2) == 0;
    assert PartialSum(s1, s2, 0) == 0;
  } else {
    var lastBit := s2[|s2|-1];
    var prefix := s2[0..|s2|-1];
    
    assert Str2Int(s2) == 2 * Str2Int(prefix) + (if lastBit == '1' then 1 else 0);
    
    // Prove by induction that the partial sum construction matches multiplication
    PartialSumLemma(s1, prefix);
    
    // The math works out due to the binary representation
    assert Str2Int(s1) * Str2Int(s2) == 
           Str2Int(s1) * (2 * Str2Int(prefix) + (if lastBit == '1' then 1 else 0));
    assert Str2Int(s1) * Str2Int(s2) == 
           2 * Str2Int(s1) * Str2Int(prefix) + (if lastBit == '1' then Str2Int(s1) else 0);
  }
}

// ----------------------------------------------------
// string-based multiplication
//    No direct use of Str2Int/Int2Str
// ----------------------------------------------------
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  /* code modified by LLM (iteration 1): Handle edge cases first */
  if |s1| == 0 || |s2| == 0 {
    res := "0";
    return;
  }
  
  if s1 == "0" || s2 == "0" {
    res := "0";
    return;
  }
  
  /* code modified by LLM (iteration 1): Initialize result to "0" */
  res := "0";
  
  /* code modified by LLM (iteration 1): Iterate through each bit of s2 from right to left */
  var i := 0;
  
  /* code modified by LLM (iteration 1): Use mathematical partial sum for loop invariant */
  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant ValidBitString(res)
    invariant Str2Int(res) == PartialSum(s1, s2, i)
    decreases |s2| - i
  {
    /* code modified by LLM (iteration 1): Check if current bit (from right) is 1 */
    var bitIndex := |s2| - 1 - i;
    if s2[bitIndex] == '1' {
      /* code modified by LLM (iteration 1): Create shifted version of s1 */
      var shifted := s1 + Zeros(i);
      ConcatZerosLemma(s1, i);
      
      /* code modified by LLM (iteration 1): Add shifted value to result */
      res := Add(res, shifted);
    }
    
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Apply final lemma to prove correctness */
  PartialSumLemma(s1, s2);
  assert Str2Int(res) == PartialSum(s1, s2, |s2|);
  assert PartialSum(s1, s2, |s2|) == Str2Int(s1) * Str2Int(s2);
}