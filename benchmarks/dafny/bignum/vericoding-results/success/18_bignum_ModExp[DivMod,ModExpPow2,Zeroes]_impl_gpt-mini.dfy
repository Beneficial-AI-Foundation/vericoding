ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
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

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  assume{:axiom} false;
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
method ExpIntSucc(x: nat, k: nat)
  ensures Exp_int(x, k+1) == Exp_int(x, k) * x
  decreases k
{
  if k == 0 {
    // Exp_int(x,1) == x * Exp_int(x,0)
    assert Exp_int(x, 1) == x * Exp_int(x, 0);
    return;
  } else {
    // By the definition of Exp_int, for k > 0 we have the unfolding
    assert Exp_int(x, k+1) == x * Exp_int(x, k);
    return;
  }
}

method BitsToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    n := 0;
    return;
  }
  var prefix := s[0..|s|-1];
  var bit := if s[|s|-1] == '1' then 1 else 0;
  var p := BitsToNat(prefix);
  n := 2 * p + bit;
  return;
}

method NatToBits(n: nat) returns (r: string)
  ensures ValidBitString(r)
  ensures Str2Int(r) == n
  decreases n
{
  if n == 0 {
    r := "";
    return;
  }
  var q := n / 2;
  var pref := NatToBits(q);
  if n % 2 == 1 {
    r := pref + "1";
  } else {
    r := pref + "0";
  }
  return;
}
// </vc-helpers>

// <vc-spec>
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  //requires y < Exp_int(2,n+1)
  requires |sy| > 0 && Str2Int(sz) > 1 //&& n > 0
  decreases |sy|
// </vc-spec>
// <vc-code>
{
  var base := BitsToNat(sx);
  var exp := BitsToNat(sy);
  var m := BitsToNat(sz);
  var pow := 1;
  var i := exp;
  while i > 0
    invariant 0 <= i <= exp
    invariant pow == Exp_int(base, exp - i)
    decreases i
  {
    var k := exp - i;
    ExpIntSucc(base, k);
    // pow == Exp_int(base, k)
    pow := pow * base;
    // now pow == Exp_int(base, k+1)
    assert pow == Exp_int(base, k+1);
    i := i - 1;
  }
  var rem := pow % m;
  res := NatToBits(rem);
  return;
}
// </vc-code>

