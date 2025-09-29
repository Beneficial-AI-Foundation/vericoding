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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
function NatToBin(n: nat): string
  ensures ValidBitString(NatToBin(n))
  ensures Str2Int(NatToBin(n)) == n
  decreases n
{
  if n == 0 then "" else NatToBin(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Str2Int_PrefixAppend(s: string, i: int)
  requires ValidBitString(s)
  requires 0 <= i < |s|
  ensures Str2Int(s[0..i+1]) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0)
  decreases |s| - i
{
  var t := s[0..i+1];
  assert |t| == i + 1;
  assert t[0..|t|-1] == s[0..i];
  assert t[|t|-1] == s[i];
  if |t| == 0 {
    // impossible
  } else {
    assert Str2Int(t) == 2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
    assert Str2Int(t) == 2 * Str2Int(s[0..i]) + (if s[i] == '1' then 1 else 0);
  }
}

lemma Str2Int_AppendBit(s: string, bit: int)
  requires ValidBitString(s)
  requires bit == 0 || bit == 1
  ensures ValidBitString(s + (if bit == 1 then "1" else "0"))
  ensures Str2Int(s + (if bit == 1 then "1" else "0")) == 2 * Str2Int(s) + bit
  decreases |s|
{
  var t := s + (if bit == 1 then "1" else "0");
  assert ValidBitString(t);
  Str2Int_PrefixAppend(t, |t|-1);
  assert t[0..|t|-1] == s;
  assert (if t[|t|-1] == '1' then 1 else 0) == bit;
  assert Str2Int(t) == 2 * Str2Int(s) + bit;
}

lemma NatToBin_correct(n: nat)
  ensures ValidBitString(NatToBin(n))
  ensures Str2Int(NatToBin(n)) == n
  decreases n
{
  if n == 0 {
    // NatToBin(0) == ""
    assert Str2Int(NatToBin(0)) == 0;
    assert ValidBitString(NatToBin(0));
  } else {
    NatToBin_correct(n / 2);
    var s := NatToBin(n / 2);
    assert Str2Int(s) == n / 2;
    Str2Int_AppendBit(s, n % 2);
    assert Str2Int(NatToBin(n)) == 2 * Str2Int(s) + n % 2;
    assert n == 2 * (n / 2) + n % 2;
    assert Str2Int(NatToBin(n)) == n;
    assert ValidBitString(NatToBin(n));
  }
}

lemma Exp_int_step(x: nat, i: nat)
  ensures Exp_int(x, i + 1) == x * Exp_int(x, i)
{
  if i + 1 == 0 {
  } else {
    assert Exp_int(x, i + 1) == x * Exp_int(x, i);
  }
}

method ParseBin(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
    decreases |s| - i
  {
    var oldi := i;
    var bit := (if s[i] == '1' then 1 else 0);
    n := 2 * n + bit;
    i := i + 1;
    Str2Int_PrefixAppend(s, oldi);
  }
  // i == |s| here; prove final postcondition
  assert i == |s|;
  // s[0..|s|] is equal to s
  assert s[0..i] == s;
  assert n == Str2Int(s[0..i]);
  assert n == Str2Int(s);
}

method ModPowExec(x: nat, e: nat, m: nat) returns (r: nat)
  requires m > 0
  ensures r == Exp_int(x, e) % m
{
  var p := 1;
  var i := 0;
  while i < e
    invariant 0 <= i <= e
    invariant p == Exp_int(x, i)
    decreases e - i
  {
    var oldi := i;
    p := p * x;
    i := i + 1;
    Exp_int_step(x, oldi);
    assert p == Exp_int(x, i);
  }
  r := p % m;
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
  var x := ParseBin(sx);
  var y := ParseBin(sy);
  var m := ParseBin(sz);
  assert x == Str2Int(sx);
  assert y == Str2Int(sy);
  assert m == Str2Int(sz);
  assert m > 0;
  var rr := ModPowExec(x, y, m);
  assert rr == Exp_int(x, y) % m;
  assert rr == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  res := NatToBin(rr);
  NatToBin_correct(rr);
  assert Str2Int(res) == rr;
  assert ValidBitString(res);
}
// </vc-code>

