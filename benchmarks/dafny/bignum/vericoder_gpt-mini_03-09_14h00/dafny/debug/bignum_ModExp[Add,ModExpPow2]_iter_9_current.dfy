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
function method ModPow(a: nat, b: nat, m: nat): nat
  decreases b
{
  if m == 0 then 0 // undefined modulus; kept to ensure totality (will not be used with m==0)
  else if b == 0 then 1 % m
  else if b % 2 == 0 then (ModPow(a, b/2, m) * ModPow(a, b/2, m)) % m
  else (a % m * ModPow(a, b-1, m)) % m
}

lemma ModPow_correct(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ModPow(a, b, m) == Exp_int(a, b) % m
  decreases b
{
  if b == 0 {
    // ModPow(a,0,m) == 1 % m and Exp_int(a,0) == 1
  } else if b % 2 == 0 {
    ModPow_correct(a, b/2, m);
    // Let t = ModPow(a,b/2,m). Then
    // ModPow(a,b,m) = (t*t) % m
    // By IH t == Exp_int(a,b/2) % m
    // So ModPow(a,b,m) == (Exp_int(a,b/2) % m * Exp_int(a,b/2) % m) % m
    // which equals (Exp_int(a,b/2) * Exp_int(a,b/2)) % m
    // and Exp_int(a,b) == Exp_int(a,b/2) * Exp_int(a,b/2)
  } else {
    ModPow_correct(a, b-1, m);
    // By IH ModPow(a,b-1,m) == Exp_int(a,b-1) % m
    // And ModPow(a,b,m) == (a % m * ModPow(a,b-1,m)) % m
    // So ModPow(a,b,m) == (a % m * Exp_int(a,b-1) % m) % m == (a * Exp_int(a,b-1)) % m == Exp_int(a,b) % m
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
  var a := BinToNat(sx);
  var b := BinToNat(sy);
  var m := BinToNat(sz);

  assert a == Str2Int(sx);
  assert b == Str2Int(sy);
  assert m == Str2Int(sz);

  assert m != 0;

  var r := ModPow(a, b, m);

  res := NatToBin(r);

  assert ValidBitString(res);
  assert BinToNat(res) == r;
  assert BinToNat(res) == Str2Int(res);

  ModPow_correct(a, b, m);
  assert r == Exp_int(a, b) % m;

  assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
}
// </vc-code>

