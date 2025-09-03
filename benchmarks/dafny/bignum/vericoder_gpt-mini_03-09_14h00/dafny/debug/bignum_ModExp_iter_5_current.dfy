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

// <vc-helpers>
ghost lemma MulMod(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x * y) % m == ((x % m) * (y % m)) % m
{
  var xm := x % m;
  var xq := x / m;
  var ym := y % m;
  var yq := y / m;
  assert x == xm + m * xq;
  assert y == ym + m * yq;
  assert x * y == (xm + m * xq) * (ym + m * yq);
  assert x * y == xm * ym + m * (xm * yq + xq * ym + m * xq * yq);
  assert (x * y) % m == (xm * ym) % m;
  assert ((x % m) * (y % m)) % m == (xm * ym) % m;
}

ghost lemma Exp_add(b: nat, n: nat, m: nat)
  ensures Exp_int(b, n + m) == Exp_int(b, n) * Exp_int(b, m)
  decreases m
{
  if m == 0 {
    // Exp_int(b, n + 0) == Exp_int(b,n) and Exp_int(b,0) == 1
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
ghost lemma MulMod(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x * y) % m == ((x % m) * (y % m)) % m
{
  var xm := x % m;
  var xq := x / m;
  var ym := y % m;
  var yq := y / m;
  assert x == xm + m * xq;
  assert y == ym + m * yq;
  assert x * y == (xm + m * xq) * (ym + m * yq);
  assert x * y == xm * ym + m * (xm * yq + xq * ym + m * xq * yq);
  assert (x * y) % m == (xm * ym) % m;
  assert ((x % m) * (y % m)) % m == (xm * ym) % m;
}

ghost lemma Exp_add(b: nat, n: nat, m: nat)
  ensures Exp_int(b, n + m) == Exp_int(b, n) * Exp_int(b, m)
  decreases m
{
  if m == 0 {
    // Exp_int(b, n + 0) == Exp_int(b,n) and Exp_int(b,0) == 1
  }
// </vc-code>

