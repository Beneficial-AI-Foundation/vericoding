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
method StrToNat(s: string) returns (n: nat)
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
    n := 2 * n + (if s[i] == '1' then 1 else 0);
    i := i + 1;
  }
}

method NatToStr(n: nat) returns (s: string)
  ensures Str2Int(s) == n
  ensures ValidBitString(s)
{
  if n == 0 {
    s := "0";
    return;
  }
  var x := n;
  s := "";
  while x > 0
    invariant 0 <= x
    invariant ValidBitString(s)
    invariant n == x * Exp_int(2, |s|) + Str2Int(s)
    decreases x
  {
    var r := x % 2;
    s := (if r == 1 then "1" else "0") + s;
    x := x / 2;
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
  var base := StrToNat(sx);
  var exponent := StrToNat(sy);
  var modulus := StrToNat(sz);
  ghost var base0 := base;
  ghost var exp0 := exponent;
  ghost var mod0 := modulus;
  var ans := 1 % modulus;
  var b := base % modulus;
  var e := exponent;
  while e > 0
    invariant e >= 0
    invariant 0 <= ans < modulus
    invariant 0 <= b < modulus
    invariant Exp_int(base0, exp0) % mod0 == (ans * Exp_int(b, e)) % mod0
    decreases e
  {
    if e % 2 == 1 {
      ans := (ans * b) % modulus;
    }
    b := (b * b) % modulus;
    e := e / 2;
  }
  res := NatToStr(ans);
}
// </vc-code>

