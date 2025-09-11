```vc-helpers
method BitsToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases |s|
{
  n := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
    decreases |s| - i
  {
    n := 2 * n + (if s[i] == '1' then 1 else 0);
    i := i + 1;
  }
}

method IntToBin(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "0";
    return;
  }
  s := "";
  var k := n;
  while k > 0
    invariant k >= 0
    invariant ValidBitString(s)
    invariant n == k * Exp_int(2, |s|) + Str2Int(s)
    decreases k
  {
    var b := if k % 2 == 1 then "1" else "0";
    s := s + b;
    k := k / 2;
  }
}

lemma ModMulDistrib(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
  var qa := a / m;
  var ra := a % m;
  var qb := b / m;
  var rb := b % m;
  assert a == m * qa + ra;
  assert b == m * qb + rb;
  calc {
    a * b;
    == (m * qa + ra) * (m * qb + rb);
    == m * (qa * (m * qb + rb)) + ra * (m * qb + rb);
    == m * (qa * m * qb + qa * rb) + ra * (m * qb + rb);
    == m * (qa * m * qb + qa * rb + ra * qb) + ra * rb;
  }
  // So a*b = m*K + ra*rb, hence remainder modulo m is ra*rb % m
  assert (a * b) % m == (ra * rb) % m;
  assert (ra * rb) % m == ((a % m) * (b % m)) % m;
}

lemma PowModSquare(a: nat, e: nat, m: nat)
  requires m > 0
  ensures ((Exp_int(a, e) % m) * (Exp_int(a, e) % m)) % m == Exp_int(a, 2 * e) % m
{
  var x := Exp_int(a, e);
  ModMulDistrib(x, x, m);
  assert Exp_int(a, 2 * e) == x * x;
}

method ModExpRec(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz) && Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases |sy|
{
  if |sy| == 0 {
    var m := BitsToNat(sz);
    var v := 1 % m;
    res := IntToBin(v);
    return;
  }

  var sy0 := sy[0..|sy|-1];
  var lastBit := (if sy[|sy|-1] == '1' then 1 else 0);

  var t := ModExpRec(sx, sy0, sz);
  var tval := BitsToNat(t);
  var m := BitsToNat(sz);
  var a := BitsToNat(sx);

  // sq = (tval * tval) % m, and by lemma equals Exp_int(a, 2*e') % m
  var sq := (tval * tval) % m;
  if lastBit == 1 {
    var v := (sq * (