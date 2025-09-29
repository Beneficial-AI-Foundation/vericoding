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

// <vc-helpers>
function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Int2StrCorrect(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  // Proof by induction follows from the definition
}

lemma Str2IntNonNegative(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) >= 0
{
  // Follows from definition since Str2Int returns nat
}

lemma Str2IntMultiplicative(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(Int2Str(Str2Int(s1) * Str2Int(s2))) == Str2Int(s1) * Str2Int(s2)
{
  Int2StrCorrect(Str2Int(s1) * Str2Int(s2));
}

lemma ValidBitStringConcat(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(s1 + s2)
{
  // Follows from definition of ValidBitString
}

function Str2IntFunc(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2IntFunc(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

lemma Str2IntEquivalence(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2IntFunc(s)
{
  // Follows from identical definitions
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var val1 := Str2IntFunc(s1);
  var val2 := Str2IntFunc(s2);
  var product := val1 * val2;
  res := Int2Str(product);
  
  Str2IntEquivalence(s1);
  Str2IntEquivalence(s2);
}
// </vc-code>

