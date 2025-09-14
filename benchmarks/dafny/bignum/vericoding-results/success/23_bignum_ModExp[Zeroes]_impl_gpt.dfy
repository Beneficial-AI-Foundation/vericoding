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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Nat2Bits(n: nat): string
  ensures ValidBitString(Nat2Bits(n))
  ensures Str2Int(Nat2Bits(n)) == n
  decreases n
{
  if n == 0 then
    ""
  else
    Nat2Bits(n/2) + (if n % 2 == 1 then "1" else "0")
}

function Bits2Nat(s: string): nat
  requires ValidBitString(s)
  ensures Bits2Nat(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * Bits2Nat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function Pow(x: nat, y: nat): nat
  ensures Pow(x, y) == Exp_int(x, y)
  decreases y
{
  if y == 0 then 1 else x * Pow(x, y - 1)
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
  var a := Bits2Nat(sx);
  var b := Bits2Nat(sy);
  var m := Bits2Nat(sz);
  assert a == Str2Int(sx);
  assert b == Str2Int(sy);
  assert m == Str2Int(sz);
  assert m > 1;
  var k := Pow(a, b) % m;
  res := Nat2Bits(k);
}
// </vc-code>

