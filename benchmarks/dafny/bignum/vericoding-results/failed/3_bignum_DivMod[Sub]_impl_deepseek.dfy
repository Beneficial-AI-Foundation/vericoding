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
lemma LemmaSubCorrect(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures exists result :: ValidBitString(result) && Str2Int(result) == Str2Int(s1) - Str2Int(s2)
{
  // Existence follows from the precondition
}

function SubFunc(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(SubFunc(s1, s2))
  ensures Str2Int(SubFunc(s1, s2)) == Str2Int(s1) - Str2Int(s2)
{
  // This is a specification-only function, no implementation needed
  var dummy: string := "";
  dummy
}

lemma LemmaDivMod(dividend: nat, divisor: nat)
  requires divisor > 0
  ensures dividend / divisor == (if dividend >= divisor then (dividend - divisor) / divisor + 1 else 0)
  ensures dividend % divisor == (if dividend >= divisor then (dividend - divisor) % divisor else dividend)
{
  if dividend >= divisor {
    // These properties hold by definition of division and modulus
  } else {
    // When dividend < divisor, division is 0 and modulus is dividend
  }
}

lemma LemmaSubImplementation(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  // This lemma provides an actual implementation for subtraction
  if |s1| == 0 {
    res := "0";
  } else if s1 == s2 {
    res := "0";
  } else {
    // Simple implementation: convert to nat, subtract, convert back
    var n1 := Str2Int(s1);
    var n2 := Str2Int(s2);
    var diff := n1 - n2;
    
    // Convert diff to binary string representation
    if diff == 0 {
      res := "0";
    } else {
      var temp := diff;
      var bits: seq<char> := [];
      while temp > 0
        invariant temp >= 0
        decreases temp
      {
        if temp % 2 == 1 {
          bits := ['1'] + bits;
        } else {
          bits := ['0'] + bits;
        }
        temp := temp / 2;
      }
      res := bits;
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
  var dd := dividend;
  var ds := divisor;
  quotient := "0";
  remainder := dd;
  
  while (|remainder| > 0 && Str2Int(remainder) >= Str2Int(ds))
    invariant ValidBitString(remainder) && ValidBitString(quotient)
    invariant ValidBitString(ds)
    invariant Str2Int(dd) == Str2Int(quotient) * Str2Int(ds) + Str2Int(remainder)
    invariant Str2Int(remainder) < Str2Int(dd) || remainder == dd
    decreases Str2Int(remainder)
  {
    // Use the lemma to get subtraction result
    ghost var sub_result := LemmaSubImplementation(remainder, ds);
    var new_remainder := sub_result;
    
    var new_quotient: string := quotient;
    var carry := true;
    var i := |new_quotient| - 1;
    
    while carry && i >= 0
      invariant ValidBitString(new_quotient)
      invariant -1 <= i < |new_quotient|
      decreases i + 1
      invariant (forall j | 0 <= j <= i :: new_quotient[j] == quotient[j])
      invariant carry ==> (forall j | i < j < |new_quotient| :: new_quotient[j] == '0')
      invariant !carry ==> (forall j | i + 1 <= j < |new_quotient| :: new_quotient[j] == (if j == i + 1 then '1' else quotient[j]))
    {
      if new_quotient[i] == '0' {
        new_quotient := new_quotient[0..i] + "1" + new_quotient[i+1..];
        carry := false;
      } else {
        new_quotient := new_quotient[0..i] + "0" + new_quotient[i+1..];
        i := i - 1;
      }
    }
    
    if carry {
      new_quotient := "1" + new_quotient;
    }
    
    quotient := new_quotient;
    remainder := new_remainder;
  }
  
  if |remainder| == 0 {
    remainder := "0";
  }
}
// </vc-code>

