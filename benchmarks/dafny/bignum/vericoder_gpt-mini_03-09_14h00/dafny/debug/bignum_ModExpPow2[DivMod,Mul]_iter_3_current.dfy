ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Exp_int_div2(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n-1)
  ensures Exp_int(2, n) / 2 == Exp_int(2, n-1)
  ensures Exp_int(2, n) % 2 == 0
  decreases n
{
  // By the recursive definition of Exp_int, for n>0 we have Exp_int(2,n) = 2 * Exp_int(2,n-1).
  if n == 1 {
    assert Exp_int(2,1) == 2 * Exp_int(2,0);
  } else {
    // Unfolding definition:
    assert Exp_int(2,n) == 2 * Exp_int(2,n-1);
  }
  assert Exp_int(2,n) / 2 == Exp_int(2,n-1);
  assert Exp_int(2,n) % 2 == 0;
}

lemma PowerPrefixOfPowerOfTwo(s: string, n: nat)
  requires ValidBitString(s)
  requires |s| == n + 1
  requires Str2Int(s) == Exp_int(2, n)
  requires n > 0
  ensures Str2Int(s[0..|s|-1]) == Exp_int(2, n-1)
  decreases n
{
  var prefix := s[0..|s|-1];
  var last := s[|s|-1];

  // Expand Str2Int(s) by definition.
  assert Str2Int(s) == 2 * Str2Int(prefix) + (if last == '1' then 1 else 0);

  // Show Exp_int(2,n) is even, so the last bit must be 0.
  Exp_int_div2(n);
  assert Exp_int(2, n) % 2 == 0;

  // From Str2Int(s) == Exp_int(2,n) we get
  // (2*Str2Int(prefix) + bit) % 2 == 0.
  // If last == '1' then RHS would be odd, contradiction. Hence last == '0'.
  if last == '1' {
    // then Str2Int(s) is odd, but Exp_int(2,n) is even, contradiction
    assert (2 * Str2Int(prefix) + 1) % 2 == 1;
    assert Exp_int(2, n) % 2 == 0;
    assert (2 * Str2Int(prefix) + 1) % 2 != Exp_int(2, n) % 2;
    // Using Str2Int(s) == Exp_int(2,n) we reach contradiction
    assert false;
  } else {
    // last == '0'
    assert (if last == '1' then 1 else 0) == 0;
    assert Str2Int(s) == 2 * Str2Int(prefix);
    // Divide both sides by 2 and use Exp_int_div2 to conclude the result.
    assert Str2Int(prefix) == Str2Int(s) / 2;
    assert Str2Int(prefix) == Exp_int(2, n) / 2;
    Exp_int_div2(n);
    assert Str2Int(prefix) == Exp_int(2, n-1);
  }
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  if Str2Int(sy) == 0 {
    // x^0 % sz == 1 % sz == 1 since Str2Int(sz) > 1
    return "1";
  }
  if n == 0 {
    // sy must be 1 when not zero and n == 0, so x^1 % sz == x % sz
    var q, r := DivMod(sx, sz);
    return r;
  }
  // n > 0 and Str2Int(sy) == Exp_int(2,n)
  PowerPrefixOfPowerOfTwo(sy, n);
  var sy1 := sy[0..|sy|-1];
  var res1 := ModExpPow2(sx, sy1, n-1, sz);
  var prod := Mul(res1, res1);
  var q, r := DivMod(prod, sz);
  return r;
}
// </vc-code>

