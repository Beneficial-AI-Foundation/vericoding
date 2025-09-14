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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

predicate ValidBitString(s: string)
{
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
  s := "";
  var i := 0;
  while i < n
    invariant |s| == i
    invariant ValidBitString(s)
    invariant AllZero(s)
    invariant Str2Int(s) == 0
  {
    s := s + "0";
    i := i + 1;
  }
}

function Int2Str(x: nat): string
  ensures ValidBitString(Int2Str(x))
  ensures Str2Int(Int2Str(x)) == x
{
  if x == 0 then "0"
  else if x == 1 then "1"
  else Str2Int((x / 2)) + (if x % 2 == 0 then "0" else "1")
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
  if |sy| == 1 {
    if sy == "0" {
      res := "1"; // x^0 = 1
    } else { // sy == "1"
      var sx_int_val_local := Str2Int(sx);
      var sz_int_val_local := Str2Int(sz);
      res := Int2Str(sx_int_val_local % sz_int_val_local); // x^1 = x (mod z)
    }
  } else {
    var y_prime_str := sy[0..|sy|-1]; // sy / 2 with truncation
    var y_last_bit := sy[|sy|-1];

    var rec_res_str := ModExp(sx, y_prime_str, sz);
    var rec_res_int := Str2Int(rec_res_str);
    var sx_int_val_local := Str2Int(sx);
    var sz_int_val_local := Str2Int(sz);

    var res_int_val_local := (rec_res_int * rec_res_int) % sz_int_val_local;
    if y_last_bit == '1' {
      res_int_val_local := (res_int_val_local * sx_int_val_local) % sz_int_val_local;
    }
    res := Int2Str(res_int_val_local);
  }
}
// </vc-code>

