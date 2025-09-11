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

method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{
  // By definition of Str2Int
}

lemma Str2IntZero()
  ensures Str2Int("0") == 0
{
  calc {
    Str2Int("0");
    == { assert "0" == "0"[0..1]; }
    2 * Str2Int("0"[0..0]) + 0;
    == { assert "0"[0..0] == ""; }
    2 * Str2Int("") + 0;
    == 2 * 0 + 0;
    == 0;
  }
}

lemma Str2IntOne()
  ensures Str2Int("1") == 1
{
  calc {
    Str2Int("1");
    == { assert "1" == "1"[0..1]; }
    2 * Str2Int("1"[0..0]) + 1;
    == { assert "1"[0..0] == ""; }
    2 * Str2Int("") + 1;
    == 2 * 0 + 1;
    == 1;
  }
}

lemma Str2IntAppend(s: string, c: char)
  requires ValidBitString(s)
  requires c == '0' || c == '1'
  ensures ValidBitString(s + [c])
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
  var sc := s + [c];
  assert sc[0..|sc|-1] == s;
  assert sc[|sc|-1] == c;
}

method AddOne(s: string) returns (res: string)
  requires ValidBitString(s)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) + 1
{
  if |s| == 0 {
    res := "1";
    Str2IntOne();
    Str2IntEmpty();
  } else if s[|s|-1] == '0' {
    var prefix := s[0..|s|-1];
    res := prefix + "1";
    Str2IntAppend(prefix, '1');
    Str2IntAppend(prefix, '0');
    assert Str2Int(res) == 2 * Str2Int(prefix) + 1;
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0;
  } else {
    assert s[|s|-1] == '1';
    var prefix := s[0..|s|-1];
    if |prefix| == 0 {
      res := "10";
      calc {
        Str2Int("10");
        == 2 * Str2Int("1") + 0;
        == { Str2IntOne(); }
        2 * 1 + 0;
        == 2;
      }
      Str2IntOne();
    } else {
      var prefixPlusOne := AddOne(prefix);
      res := prefixPlusOne + "0";
      Str2IntAppend(prefixPlusOne, '0');
      Str2IntAppend(prefix, '1');
      assert Str2Int(res) == 2 * Str2Int(prefixPlusOne) + 0;
      assert Str2Int(prefixPlusOne) == Str2Int(prefix) + 1;
      assert Str2Int(s) == 2 * Str2Int(prefix) + 1;
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
  quotient := "0";
  remainder := dividend;
  
  Str2IntZero();
  
  var cmp := Compare(remainder, divisor);
  
  while cmp >= 0
    invariant ValidBitString(quotient)
    invariant ValidBitString(remainder)
    invariant Str2Int(dividend) == Str2Int(quotient) * Str2Int(divisor) + Str2Int(remainder)
    invariant 0 <= Str2Int(remainder)
    invariant cmp == -1 ==> Str2Int(remainder) < Str2Int(divisor)
    invariant cmp == 0 ==> Str2Int(remainder) == Str2Int(divisor)
    invariant cmp == 1 ==> Str2Int(remainder) > Str2Int(divisor)
    invariant cmp >= 0 ==> Str2Int(remainder) >= Str2Int(divisor)
    decreases Str2Int(remainder)
  {
    remainder := Sub(remainder, divisor);
    quotient := AddOne(quotient);
    cmp := Compare(remainder, divisor);
  }
}
// </vc-code>

