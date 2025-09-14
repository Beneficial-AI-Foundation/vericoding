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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExpModLemma(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == (if y == 0 then 1 % z else (x * Exp_int(x, y - 1)) % z)
{
}

lemma ExpModLemma2(x: nat, y: nat, z: nat)
  requires z > 1
  ensures (x * y) % z == (x % z) * (y % z) % z
{
}

lemma ExpModLemma3(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z
  decreases y
{
  if y == 0 {
  } else {
    ExpModLemma3(x, y - 1, z);
    calc {
      Exp_int(x, y) % z;
      == { ExpModLemma(x, y, z); }
      (x * Exp_int(x, y - 1)) % z;
      == { ExpModLemma2(x, Exp_int(x, y - 1), z); }
      (x % z) * (Exp_int(x, y - 1) % z) % z;
      == { ExpModLemma3(x, y - 1, z); }
      (x % z) * (Exp_int(x % z, y - 1) % z) % z;
      == { ExpModLemma2(x % z, Exp_int(x % z, y - 1), z); }
      ((x % z) * Exp_int(x % z, y - 1)) % z;
      == 
      Exp_int(x % z, y) % z;
    }
  }
}

ghost function ModExpHelper(x: nat, y: nat, z: nat): nat
  requires z > 1
  ensures ModExpHelper(x, y, z) == Exp_int(x, y) % z
  decreases y
{
  if y == 0 then
    1 % z
  else if y % 2 == 1 then
    (x * ModExpHelper(x, y - 1, z)) % z
  else
    var half := ModExpHelper(x, y / 2, z);
    (half * half) % z
}

ghost function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 then "0"
  else if n % 2 == 0 then Int2Str(n / 2) + "0"
  else Int2Str(n / 2) + "1"
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
  var x := Str2Int(sx);
  var y := Str2Int(sy);
  var z := Str2Int(sz);
  
  if y == 0 {
    var one_str := "1";
    res := one_str;
  } else {
    var tmp := ModExpHelper(x, y, z);
    var tmp_str := Int2Str(tmp);
    res := tmp_str;
  }
}
// </vc-code>

