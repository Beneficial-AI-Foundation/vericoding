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

// <vc-helpers>
ghost function Int2Str(v: nat): string
  ensures ValidBitString(result)
  ensures Str2Int(result) == v
  decreases v
{
  if v == 0 then "" else Int2Str(v / 2) + (if v % 2 == 1 then "1" else "0")
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
  var m := Str2Int(sz);
  var e := Str2Int(sy);
  if e == 0 {
    res := Int2Str(1 % m);
    return;
  }
  var r := Str2Int(sx) % m;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r < m
    decreases n - i
  {
    r := (r * r) % m;
    i := i + 1;
  }
  res := Int2Str(r);
}
// </vc-code>

