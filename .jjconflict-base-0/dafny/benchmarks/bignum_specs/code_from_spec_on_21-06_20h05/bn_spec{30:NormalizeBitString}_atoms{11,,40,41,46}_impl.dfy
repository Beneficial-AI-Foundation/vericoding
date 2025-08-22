// ATOM
// BN_46
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// ATOM
//BN_11
function Exp_int(x: nat, y:nat): nat  
{
  if y == 0 then 1 else x * Exp_int(x, y-1)
}

// ATOM
// BN_40
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

/* code modified by LLM (iteration 1): Added helper lemma to prove that removing leading zeros preserves integer value */
lemma LeadingZeroLemma(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[0] == '0'
  ensures Str2Int(s) == Str2Int(s[1..])
{
  if |s| == 1 {
    // s == "0", s[1..] == ""
    // Str2Int("0") == 0, Str2Int("") == 0
  } else {
    // Use Str2IntLemma with i = 0
    Str2IntLemma(s, 0);
    // This gives us: Str2Int(s) == Str2Int(s[..1]) * Exp_int(2, |s|-1) + Str2Int(s[1..])
    // Since s[..1] == "0", we have Str2Int(s[..1]) == 0
    // So Str2Int(s) == 0 * Exp_int(2, |s|-1) + Str2Int(s[1..]) == Str2Int(s[1..])
  }
}

/* code modified by LLM (iteration 1): Added helper lemma to prove substring validity */
lemma SubstringValidLemma(s: string, i: nat)
  requires ValidBitString(s)
  requires 0 <= i <= |s|
  ensures ValidBitString(s[i..])
{
  // This follows directly from the definition of ValidBitString
}

// IMPL BN_30
method NormalizeBitString(s: string) returns(t: string) 
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  if !ValidBitString(s) {
    t := "0";
  } else if |s| == 0 {
    t := "0";
  } else {
    var i := 0;
    /* code modified by LLM (iteration 1): Added ghost variable to track original string value */
    ghost var original_value := Str2Int(s);
    
    while i < |s| && s[i] == '0'
      invariant 0 <= i <= |s|
      /* code modified by LLM (iteration 1): Added invariant to maintain integer value equality */
      invariant ValidBitString(s[i..])
      invariant Str2Int(s) == Str2Int(s[i..])
    {
      /* code modified by LLM (iteration 1): Added proof that substring is valid */
      SubstringValidLemma(s, i);
      /* code modified by LLM (iteration 1): Added proof that removing leading zero preserves value */
      LeadingZeroLemma(s[i..]);
      i := i + 1;
    }
    
    if i == |s| {
      t := "0";
      /* code modified by LLM (iteration 1): Added assertion to help verification */
      assert Str2Int(s[i..]) == 0; // s[i..] is empty string
    } else {
      t := s[i..];
      /* code modified by LLM (iteration 1): Added proof that final substring is valid */
      SubstringValidLemma(s, i);
    }
  }
}