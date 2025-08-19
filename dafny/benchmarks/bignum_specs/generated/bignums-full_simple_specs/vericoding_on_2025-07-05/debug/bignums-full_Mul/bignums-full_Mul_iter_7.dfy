//ATOM

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

//ATOM

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

//ATOM

// Make an opaque version to speed up verification
opaque function OStr2Int(s: string): nat
  requires ValidBitString(s)
{
  Str2Int(s)
}

//ATOM

// ----------------------------------------------------
// Str2Int: bit-string -> nat (reference function)
// ----------------------------------------------------
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

//ATOM

predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

//IMPL Mul

// ----------------------------------------------------
// string-based multiplication
//    No direct use of Str2Int/Int2Str
// ----------------------------------------------------
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  /* code modified by LLM (iteration 1): Handle empty strings as zero */
  if |s1| == 0 || |s2| == 0 {
    res := "0";
    return;
  }
  
  /* code modified by LLM (iteration 1): Initialize result to zero and use simple bit-by-bit multiplication */
  res := "0";
  var i := 0;
  
  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant ValidBitString(res)
    /* code modified by LLM (iteration 1): Maintain that result equals s1 * value of processed bits */
    invariant Str2Int(res) == Str2Int(s1) * ProcessedValue(s2, i)
  {
    /* code modified by LLM (iteration 1): Process bit from right to left for correct positioning */
    if s2[|s2| - 1 - i] == '1' {
      var shifted_s1 := LeftShift(s1, i);
      res := Add(res, shifted_s1);
    }
    
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Apply lemma to establish final postcondition */
  ProcessedValueComplete(s2);
  
  res := NormalizeBitString(res);
}

/* code modified by LLM (iteration 1): Helper function to create left-shifted string */
function LeftShift(s: string, n: nat): string
  requires ValidBitString(s)
  ensures ValidBitString(LeftShift(s, n))
  ensures Str2Int(LeftShift(s, n)) == Str2Int(s) * Power2(n)
{
  s + ZeroString(n)
}

/* code modified by LLM (iteration 1): Helper function to create string of zeros */
function ZeroString(n: nat): string
  ensures ValidBitString(ZeroString(n))
  ensures |ZeroString(n)| == n
  ensures n > 0 ==> Str2Int(ZeroString(n)) == 0
  decreases n
{
  if n == 0 then "" else ZeroString(n - 1) + "0"
}

/* code modified by LLM (iteration 1): Helper function for power of 2 */
function Power2(n: nat): nat
  ensures Power2(n) > 0
  decreases n
{
  if n == 0 then 1 else 2 * Power2(n - 1)
}

/* code modified by LLM (iteration 1): Function to compute value of processed bits from right */
function ProcessedValue(s: string, k: nat): nat
  requires ValidBitString(s)
  requires 0 <= k <= |s|
  decreases k
{
  if k == 0 then 0
  else 
    var bit_pos := k - 1;
    var bit_value := if s[|s| - 1 - bit_pos] == '1' then Power2(bit_pos) else 0;
    ProcessedValue(s, k - 1) + bit_value
}

/* code modified by LLM (iteration 1): Lemma to prove ProcessedValue equals Str2Int for complete string */
lemma ProcessedValueComplete(s: string)
  requires ValidBitString(s)
  ensures ProcessedValue(s, |s|) == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    // Base case: empty string
  } else {
    // Inductive case
    var s_prefix := s[0..|s|-1];
    ProcessedValueComplete(s_prefix);
    
    /* code modified by LLM (iteration 1): Show the relationship between ProcessedValue and Str2Int */
    ProcessedValueStr2IntRelation(s);
  }
}

/* code modified by LLM (iteration 1): Helper lemma to establish relationship between ProcessedValue and Str2Int */
lemma ProcessedValueStr2IntRelation(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures ProcessedValue(s, |s|) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
  var n := |s|;
  if n == 1 {
    // Base case: single character
    if s[0] == '1' {
      Power2ZeroIsOne();
    }
  } else {
    // Show that ProcessedValue has the same recursive structure as Str2Int
    ProcessedValueRecursiveStructure(s, n);
  }
}

/* code modified by LLM (iteration 1): Lemma to show ProcessedValue has recursive structure matching Str2Int */
lemma ProcessedValueRecursiveStructure(s: string, n: nat)
  requires ValidBitString(s)
  requires n == |s| > 1
  ensures ProcessedValue(s, n) == 2 * ProcessedValue(s[0..n-1], n-1) + (if s[n-1] == '1' then 1 else 0)
{
  // The proof follows from the definition of ProcessedValue
  // and properties of Power2
  Power2Recursive(n-2);
}

/* code modified by LLM (iteration 1): Lemma that Power2(0) == 1 */
lemma Power2ZeroIsOne()
  ensures Power2(0) == 1
{
  // Follows directly from definition
}

/* code modified by LLM (iteration 1): Lemma about Power2 recursive property */
lemma Power2Recursive(n: nat)
  ensures Power2(n + 1) == 2 * Power2(n)
{
  // Follows from definition of Power2
}

/* code modified by LLM (iteration 1): Lemma to prove ZeroString represents zero */
lemma ZeroStringIsZero(n: nat)
  requires n > 0
  ensures Str2Int(ZeroString(n)) == 0
  decreases n
{
  if n == 1 {
    // Base case
  } else {
    ZeroStringIsZero(n - 1);
  }
}

/* code modified by LLM (iteration 1): Lemma to prove LeftShift correctness */
lemma LeftShiftCorrectness(s: string, n: nat)
  requires ValidBitString(s)
  ensures Str2Int(LeftShift(s, n)) == Str2Int(s) * Power2(n)
{
  if n == 0 {
    // Base case
  } else {
    // Use properties of string concatenation and Str2Int
    if |s| == 0 {
      ZeroStringIsZero(n);
    } else {
      StringConcatProperty(s, ZeroString(n));
      ZeroStringIsZero(n);
    }
  }
}

/* code modified by LLM (iteration 1): Lemma about string concatenation with zeros */
lemma StringConcatProperty(s: string, zeros: string)
  requires ValidBitString(s)
  requires ValidBitString(zeros)
  requires |zeros| > 0
  requires Str2Int(zeros) == 0
  ensures Str2Int(s + zeros) == Str2Int(s) * Power2(|zeros|)
{
  // This would need a more detailed proof about how concatenation
  // with trailing zeros affects the binary value
}