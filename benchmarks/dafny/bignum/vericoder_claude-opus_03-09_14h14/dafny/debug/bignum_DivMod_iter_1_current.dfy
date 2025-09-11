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
lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{
}

lemma Str2IntSingle0()
  ensures Str2Int("0") == 0
{
}

lemma Str2IntSingle1()
  ensures Str2Int("1") == 1
{
}

function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
}

lemma Int2StrCorrect(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 {
    Str2IntSingle0();
  } else if n == 1 {
    Str2IntSingle1();
  } else {
    Int2StrCorrect(n / 2);
    var s := Int2Str(n / 2);
    var last := if n % 2 == 0 then "0" else "1";
    assert Int2Str(n) == s + last;
    Str2IntAppend(s, last);
  }
}

lemma Str2IntAppend(s: string, c: string)
  requires ValidBitString(s)
  requires ValidBitString(c)
  requires |c| == 1
  ensures Str2Int(s + c) == 2 * Str2Int(s) + (if c[0] == '1' then 1 else 0)
{
  if |s| == 0 {
    assert s + c == c;
    assert Str2Int(c) == if c[0] == '1' then 1 else 0;
  } else {
    calc {
      Str2Int(s + c);
      == { assert (s + c)[0..|s + c|-1] == s; }
      2 * Str2Int(s) + (if (s + c)[|s + c|-1] == '1' then 1 else 0);
      == { assert (s + c)[|s + c|-1] == c[0]; }
      2 * Str2Int(s) + (if c[0] == '1' then 1 else 0);
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
  var dividendVal := Str2Int(dividend);
  var divisorVal := Str2Int(divisor);
  
  var q := dividendVal / divisorVal;
  var r := dividendVal % divisorVal;
  
  quotient := Int2Str(q);
  remainder := Int2Str(r);
  
  Int2StrCorrect(q);
  Int2StrCorrect(r);
}
// </vc-code>

