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
function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then
    ""
  else
    Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
}

function Str2IntM(s: string): nat
  requires ValidBitString(s)
  ensures Str2IntM(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 then
    0
  else
    2 * Str2IntM(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function Exp_intM(x: nat, y: nat): nat
  ensures Exp_intM(x, y) == Exp_int(x, y)
  decreases y
{
  if y == 0 then 1 else x * Exp_intM(x, y - 1)
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
  var nx := Str2IntM(sx);
  var ny := Str2IntM(sy);
  var nz := Str2IntM(sz);

  assert Str2Int(sx) == nx;
  assert Str2Int(sy) == ny;
  assert Str2Int(sz) == nz;
  assert nz > 0;

  var n: nat := Exp_intM(nx, ny) % nz;
  res := Int2Str(n);

  assert Str2Int(res) == n;
  assert Exp_intM(nx, ny) == Exp_int(nx, ny);
  assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
}
// </vc-code>

