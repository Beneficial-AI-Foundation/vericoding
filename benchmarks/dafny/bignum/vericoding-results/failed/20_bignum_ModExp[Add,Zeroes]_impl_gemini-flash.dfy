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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Power(base: nat, exp: nat, modulus: nat): nat
  requires modulus > 1
  decreases exp
{
  if exp == 0 then 1
  else if exp % 2 == 0 then Power((base * base) % modulus, exp / 2, modulus)
  else (base * Power((base * base) % modulus, exp / 2, modulus)) % modulus
}

method Int2BitString(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
{
  if n == 0 {
    return "0";
  }
  var temp_n := n;
  var temp_s := "";
  var n_at_entry := n;
  while temp_n > 0
    invariant ValidBitString(temp_s)
    invariant Str2Int(temp_s) * Exp_int(2, |temp_s|) + temp_n == n_at_entry
    decreases temp_n
  {
    temp_s := (if temp_n % 2 == 1 then "1" else "0") + temp_s;
    temp_n := temp_n / 2;
  }
  return temp_s;
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
    var x_int := Str2Int(sx);
    var y_int := Str2Int(sy);
    var z_int := Str2Int(sz);

    var r_int: nat := Power(x_int, y_int, z_int);
    res := Int2BitString(r_int);
}
// </vc-code>

