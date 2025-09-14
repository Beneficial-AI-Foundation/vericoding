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
function Exp(b: nat, e: nat): nat
  decreases e
{
  if e == 0 then 1 else b * Exp(b, e - 1)
}

function Power(base: nat, exp: nat): nat
  decreases exp
{
  if exp == 0 then 1 else base * Power(base, exp - 1)
}


function stringToNat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then
    0
  else
    (if s[0] == '1' then Power(2, |s| - 1) else 0) + stringToNat(s[1..])
}
// Helper function to convert a natural number to a bit string
function natToString(n: nat, len: nat): string
  requires len >= 0
  ensures ValidBitString(natToString(n,len))
  ensures (n == 0 && len == 0) || (len > 0 ==> |natToString(n,len)| == len)
  ensures len > 0 ==> Str2Int(natToString(n, len)) == n % Power(2, len)
  decreases len
{
  if len == 0 then
    ""
  else
    natToString(n/2, len-1) + (if n%2 == 0 then "0" else "1")
}

// Lemma to relate Str2Int and stringToNat
lemma Str2Int_stringToNat_equivalence(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == stringToNat(s)
  decreases s
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
    assert stringToNat(s) == 0;
  } else {
    calc {
      Str2Int(s);
      { reveal Str2Int(); }
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      { Str2Int_stringToNat_equivalence(s[0..|s|-1]); }
      2 * stringToNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    }
    calc {
      stringToNat(s);
      (if s[0] == '1' then Power(2, |s| - 1) else 0) + stringToNat(s[1..]);
    }
  }
}

lemma Exp_equality(x: nat, y: nat)
  ensures Exp_int(x, y) == Exp(x,y)
{
  if y == 0 {
    assert Exp_int(x, y) == 1;
    assert Exp(x,y) == 1;
  } else {
    Exp_equality(x, y - 1);
  }
}

lemma Str2Int_natToString_id(n: nat, len: nat)
  requires len >= 0
  requires n < Exp(2,len)
  ensures Str2Int(natToString(n, len)) == n
  decreases len
{
  if len > 0 {
    var s_prefix := natToString(n/2, len-1);
    var last_bit_char := if n%2 == 0 then "0" else "1";
    Str2Int_natToString_id(n/2, len-1);
    assert (n/2) < Power(2, len-1); // Added for verification
    calc {
      Str2Int(natToString(n, len));
      Str2Int(s_prefix + last_bit_char);
      { reveal Str2Int(); }
      2 * Str2Int(s_prefix) + (if last_bit_char == "1" then 1 else 0);
      2 * (n/2) + (if last_bit_char == "1" then 1 else 0);
      2 * (n/2) + (if n%2 == 1 then 1 else 0);
      n - (n%2) + (if n%2 == 1 then 1 else 0);
      n;
    }
  } else {
    assert n == 0;
    assert natToString(0,0) == "";
    assert Str2Int("") == 0;
  }
}

lemma Str2Int_zero_len(len: nat)
  requires len >= 1
  ensures Str2Int(natToString(0, len)) == 0
{
  calc {
    Str2Int(natToString(0, len));
    Str2Int(natToString(0/2, len-1) + "0");
    Str2Int(natToString(0,len-1) + "0");
    2 * Str2Int(natToString(0, len-1)) + 0;
  }
  if len - 1 > 0 {
    Str2Int_zero_len(len-1);
    assert Str2Int(natToString(0, len-1)) == 0;
    assert Str2Int(natToString(0, len)) == 0;
  } else {
    assert len - 1 == 0;
    assert natToString(0,0) == "";
    assert Str2Int("") == 0;
    assert Str2Int(natToString(0, len)) == 0;
  }
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
  var x_int := Str2Int(sx);
  var y_int := Str2Int(sy);
  var z_int := Str2Int(sz);

  if y_int == 0 {
    assert Exp_int(x_int, 0) == 1;
    res := natToString(1 % z_int, n + 1);
  } else {
    if sy[|sy|-1] == '0' { 
      var sy_prime_str := sy[0..|sy|-1];
      assert |sy_prime_str| == n;
      var half_res_str : string := ModExpPow2(sx, sy_prime_str, n-1, sz);
      var half_res_int := Str2Int(half_res_str);
      var final_res_int := (half_res_int * half_res_int) % z_int;
      assert (Str2Int(sy_prime_str) == Exp_int(2, n-1) || Str2Int(sy_prime_str) == 0);
      assert Exp_int(x_int, Str2Int(sy_prime_str)) % z_int == half_res_int;
      assert Exp_int(x_int, Exp_int(2,n)) == Exp_int(x_int, 2 * Exp_int(2, n-1));
      assert Exp_int(x_int, 2 * Exp_int(2, n-1)) == Exp_int(Exp_int(x_int, Exp_int(2, n-1)), 2);
      assert Exp_int(Exp_int(x_int, Exp_int(2, n-1)), 2) % z_int == (half_res_int * half_res_int) % z_int;
      res := natToString(final_res_int, n + 1);
    } else {
      assert n == 0;
      res := natToString(x_int % z_int, n + 1);
    }
  }
}
// </vc-code>

