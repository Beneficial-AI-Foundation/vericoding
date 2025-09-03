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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
method BitsToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  var i := 0;
  n := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
    decreases |s| - i
  {
    if s[i] == '1' {
      n := 2 * n + 1;
    } else {
      n := 2 * n;
    }
    i := i + 1;
  }
}

method NatToBits(n_in: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n_in
{
  if n_in == 0 {
    s := "0";
    return;
  }

  var rem := n_in;
  s := "";
  // Invariant: Str2Int(s) + rem * Exp_int(2, |s|) == n_in
  // and ValidBitString(s)
  while rem > 0
    invariant 0 <= rem <= n_in
    invariant ValidBitString(s)
    invariant Str2Int(s) + rem * Exp_int(2, |s|) == n_in
    decreases rem
  {
    var bit := rem % 2;
    if bit == 1 {
      s := "1" + s;
    } else {
      s := "0" + s;
    }
    rem := rem / 2;
  }
  // rem == 0, so Str2Int(s) == n_in
  assert rem == 0;
  assert Str2Int(s) == n_in;
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

  // Compute base^exp mod m (naive loop, easy to verify)
  var resNat := 1 % m;
  var i := 0;
  var origExp := exp;
  while i < origExp
    invariant 0 <= i <= origExp
    invariant resNat % m == Exp_int(base, i) % m
    decreases origExp - i
  {
    resNat := (resNat * base) % m;
    i := i + 1;
  }

  res := NatToBits(resNat);
}
// </vc-code>

