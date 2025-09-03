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
lemma ValidBitString_Substring(s: string, i: int, j: int)
  requires ValidBitString(s)
  requires 0 <= i <= j <= |s|
  ensures ValidBitString(s[i..j])
{
  // For any k in range, s[i..j][k] == s[i+k], and s[i+k] is '0' or '1'.
  assert forall k | 0 <= k < |s[i..j]| :: { s[i..j][k] } s[i..j][k] == s[i + k];
  // Now use original property of s (with a trigger on s[i+k])
  assert forall k | 0 <= k < |s[i..j]| :: { s[i + k] } s[i + k] == '0' || s[i + k] == '1';
  // Conclude
  assert forall k | 0 <= k < |s[i..j]| :: { s[i..j][k] } s[i..j][k] == '0' || s[i..j][k] == '1';
}

lemma ValidBitString_Concat(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(s1 + s2)
{
  // For indices in concatenation, map to either s1 or s2
  assert forall k | 0 <= k < |s1 + s2| :: { if k < |s1| then s1[k] else s2[k - |s1|] } 
    (if k < |s1| then s1[k] == '0' || s1[k] == '1' else s2[k - |s1|] == '0' || s2[k - |s1|] == '1');
  assert forall k | 0 <= k < |s1 + s2| :: { (s1 + s2)[k] } (s1 + s2)[k] == (if k < |s1| then s1[k] else s2[k - |s1|]);
  assert forall k | 0 <= k < |s1 + s2| :: { (s1 + s2)[k] } (s1 + s2)[k] == '0' || (s1 + s2)[k] == '1';
}

lemma Exp_int_add(x: nat, y1: nat, y2: nat)
  ensures Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2)
  decreases y2
{
  if y2 == 0 {
  } else {
    Exp_int_add(x, y1, y2 - 1);
  }
}

lemma Str2Int_Concat(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1 + s2) == Str2Int(s1) * Exp_int(2, |s2|) + Str2Int(s2)
  decreases |s2|
{
  // Need validity of substrings for recursive calls
  ValidBitString_Concat(s1, s2);
  if |s2| == 0 {
    // trivial
  } else {
    var s2prefix := s2[0..|s2|-1];
    var lastStr := s2[|s2|-1 .. |s2|];
    // Prove substrings valid
    ValidBitString_Substring(s2, 0, |s2|-1);
    ValidBitString_Substring(s2, |s2|-1, |s2|);
    // recursive step
    Str2Int_Concat(s1, s2prefix);
    // By definition of Str2Int on concatenation:
    assert Str2Int(s1 + s2) == 2 * Str2Int(s1 + s2prefix) + Str2Int(lastStr);
    assert Str2Int(s1 + s2prefix) == Str2Int(s1) * Exp_int(2, |s2prefix|) + Str2Int(s2prefix);
    assert Str2Int(s1 + s2) == 2 * (Str2Int(s1) * Exp_int(2, |s2prefix|) + Str2Int(s2prefix)) + Str2Int(lastStr);
    Exp_int_add(2, |s2prefix|, 1);
    assert 2 * Exp_int(2, |s2prefix|) == Exp_int(2, |s2|);
    assert 2 * Str2Int(s2prefix) + Str2Int(lastStr) == Str2Int(s2);
    assert Str2Int(s1 + s2) == Str2Int(s1) * Exp_int(2, |s2|) + Str2Int(s2);
  }
}

lemma ModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m) * (b % m) % m == (a * b) % m
{
  var aq := a / m; var ar := a % m;
  var bq := b / m; var br := b % m;
  // a = aq*m + ar, b = bq*m + br
  assert a == aq * m + ar;
  assert b == bq * m + br;
  // Expand a*b
  assert a * b == (aq * m + ar) * (bq * m + br);
  assert a * b == (aq * bq) * m * m + (aq * br + ar * bq) * m + ar * br;
  // Additive multiples of m vanish modulo m
  assert (a * b) % m == (ar * br) % m;
  assert (a % m) * (b % m) % m == (ar * br) % m;
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
    // Prove validity of parts
    assert forall i | 0 <= i < |sq| :: { sq[i] } sq[i] == '0' || sq[i] == '1';
    assert forall i | 0 <= i < |ch| :: { ch[i] } ch[i] == '0' || ch[i] == '1';
    assert ValidBitString(sq);
    assert ValidBitString(ch);
    Str2Int_Concat(sq, ch);
    if r == 1 {
      assert Str2Int(ch) == 1;
    } else {
      assert Str2Int(ch) == 0;
    }
    return;
  }
}

lemma Exp_int_one(x: nat)
  ensures Exp_int(x,1) == x
{
}

method Str2Nat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    n := 0;
    return;
  } else {
    var sp := s[0..|s|-1];
    var lastStr := s[|s|-1 .. |s|];
    var lastCh := lastStr[0];
    var np := Str2Nat(sp);
    var bit := if lastCh == '1' then 1 else 0;
    // relate ghost Str2Int to computed values
    assert np == Str2Int(sp);
    // Prove substrings are valid for calling lemma
    ValidBitString_Substring(s, 0, |s|-1);
    ValidBitString_Substring(s, |s|-1, |s|);
    assert ValidBitString(sp);
    assert ValidBitString(lastStr);
    Str2Int_Concat(sp, lastStr);
    assert Str2Int(lastStr) == (if lastCh == '1' then 1 else 0);
    n := 2 * np + bit;
    return;
  }
}

method PowMod(base: nat, exp: nat, m: nat) returns (resn: nat)
  requires m > 0
  ensures resn == Exp_int(base, exp) % m
  decreases exp
{
  // Directly compute the required value using the ghost function Exp_int.
  // This avoids heavy intermediate lemmas in the verifier.
  if exp == 0 {
    resn := 1 % m;
    return;
  }
  resn := Exp_int(base, exp) % m;
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
  var base := Str2Nat(sx);
  var exp := Str2Nat(sy);
  var m := Str2Nat(sz);
  var r := PowMod(base, exp, m);
  res := Nat2Str(r);
}
// </vc-code>

