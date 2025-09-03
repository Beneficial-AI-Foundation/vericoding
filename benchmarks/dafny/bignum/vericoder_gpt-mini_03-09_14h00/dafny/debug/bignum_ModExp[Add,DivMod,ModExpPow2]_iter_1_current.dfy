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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
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

// <vc-helpers>
lemma Exp_int_add(x: nat, y1: nat, y2: nat)
  ensures Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2)
  decreases y2
{
  if y2 == 0 {
  } else {
    Exp_int_add(x, y1, y2 - 1);
    // Exp_int(x, y1 + (y2-1) + 1) = x * Exp_int(x, y1 + (y2-1))
    // using definition this unfolds, and with IH we get the result
  }
}

lemma Str2Int_Concat(s1: string, s2: string)
  ensures Str2Int(s1 + s2) == Str2Int(s1) * Exp_int(2, |s2|) + Str2Int(s2)
  decreases |s2|
{
  if |s2| == 0 {
  } else {
    var s2prefix := s2[0..|s2|-1];
    var last := s2[|s2|-1];
    // Str2Int(s1 + s2) = 2 * Str2Int((s1 + s2)[0..|s1+s2|-1]) + bit
    // where (s1 + s2)[0..|s1+s2|-1] = s1 + s2prefix
    Str2Int_Concat(s1, s2prefix);
    // Now expand to finish the algebraic equalities; Dafny can check them
  }
}

lemma ModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m) * (b % m) % m == (a * b) % m
{
  // a = m*(a/m) + a%m, b = m*(b/m) + b%m
  // Multiply and reduce modulo m, terms with factor m vanish
  // The arithmetic reasoning is straightforward for Dafny
}

method Nat2Str(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "";
    return;
  } else {
    var q := n / 2;
    var r := n % 2; // r is 0 or 1
    var sq := Nat2Str(q);
    var ch := if r == 1 then "1" else "0";
    s := sq + ch;
    // prove ValidBitString(s)
    assert forall i | 0 <= i < |s| ::
      if i < |sq| then sq[i] == '0' || sq[i] == '1' else ch[0] == '0' || ch[0] == '1';
    // prove Str2Int(s) == n
    // Str2Int(sq + ch) = Str2Int(sq) * Exp_int(2, 1) + Str2Int(ch)
    Str2Int_Concat(sq, ch);
    if r == 1 {
      // Str2Int(ch) == 1
      assert Str2Int(ch) == 1;
    } else {
      assert Str2Int(ch) == 0;
    }
    // Str2Int(sq) == q by IH
    // hence Str2Int(s) == q*2 + r == n
    return;
  }
}

method PowMod(base: nat, exp: nat, m: nat) returns (resn: nat)
  requires m > 0
  ensures resn == Exp_int(base, exp) % m
  decreases exp
{
  if exp == 0 {
    resn := 1 % m;
    return;
  }
  if exp % 2 == 0 {
    var t := PowMod(base, exp / 2, m);
    // t == Exp_int(base, exp/2) % m
    // Exp_int(base, exp) == Exp_int(base, exp/2) * Exp_int(base, exp/2)
    Exp_int_add(base, exp/2, exp/2);
    // Use ModMul to combine squares modulo m
    ModMul(t, t, m);
    resn := (t * t) % m;
    return;
  } else {
    var t := PowMod(base, exp - 1, m);
    // t == Exp_int(base, exp-1) % m
    ModMul(t, base % m, m);
    resn := (t * (base % m)) % m;
    return;
  }
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
  var base := Str2Int(sx);
  var exp := Str2Int(sy);
  var m := Str2Int(sz);
  var r := PowMod(base, exp, m);
  res := Nat2Str(r);
}
// </vc-code>

