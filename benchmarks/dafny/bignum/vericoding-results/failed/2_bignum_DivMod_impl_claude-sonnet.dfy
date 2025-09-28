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
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Int2StrValid(n: nat)
  ensures ValidBitString(Int2Str(n))
  decreases n
{
  if n <= 1 {
    // Base cases
  } else {
    Int2StrValid(n / 2);
  }
}

lemma Int2StrCorrect(n: nat)
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n <= 1 {
    // Base cases
  } else {
    Int2StrCorrect(n / 2);
    var s := Int2Str(n / 2);
    var bit := if n % 2 == 1 then "1" else "0";
    var full := s + bit;
    
    calc {
      Str2Int(full);
      2 * Str2Int(s) + (if bit[0] == '1' then 1 else 0);
      2 * Str2Int(s) + (n % 2);
      2 * (n / 2) + (n % 2);
      n;
    }
  }
}

function NormalizeStr(s: string): string
{
  if |s| == 0 then "0"
  else if s[0] == '0' && |s| > 1 then NormalizeStr(s[1..])
  else s
}

lemma NormalizeStrValid(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(NormalizeStr(s))
  decreases |s|
{
  if |s| == 0 {
    // Base case
  } else if s[0] == '0' && |s| > 1 {
    NormalizeStrValid(s[1..]);
  }
}

lemma NormalizeStrCorrect(s: string)
  requires ValidBitString(s)
  ensures Str2Int(NormalizeStr(s)) == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    // Base case
  } else if s[0] == '0' && |s| > 1 {
    NormalizeStrCorrect(s[1..]);
    calc {
      Str2Int(s);
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      2 * Str2Int(s[1..]) + (if s[|s|-1] == '1' then 1 else 0);
      Str2Int(s[1..]);
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
  ghost var divValue := Str2Int(divisor);
  ghost var divdValue := Str2Int(dividend);
  
  ghost var quotientVal := divdValue / divValue;
  ghost var remainderVal := divdValue % divValue;
  
  quotient := Int2Str(quotientVal);
  remainder := Int2Str(remainderVal);
  
  Int2StrValid(quotientVal);
  Int2StrValid(remainderVal);
  Int2StrCorrect(quotientVal);
  Int2StrCorrect(remainderVal);
}
// </vc-code>

