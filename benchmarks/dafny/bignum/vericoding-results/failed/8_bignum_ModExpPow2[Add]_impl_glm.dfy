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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function Str2Nat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else (if s[0] == '1' then Exp_int(2, |s|-1) else 0) + Str2Nat(s[1..])
}

lemma Str2IntEqualsStr2Nat(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2Nat(s)
  decreases s
{
  if |s| == 0 {
  } else {
    calc {
      Str2Int(s);
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      2 * Str2Nat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    }
    Str2IntEqualsStr2Nat(s[0..|s|-1]);
    calc {
      Str2Nat(s);
      (if s[0] == '1' then Exp_int(2, |s|-1) else 0) + Str2Nat(s[1..]);
      (if s[|s|-1] == '1' then Exp_int(2, |s|-1) else 0) + Str2Nat(s[0..|s|-1]);
      == { assert (if s[|s|-1] == '1' then Exp_int(2, |s|-1) else 0) == (if s[|s|-1] == '1' then 1 else 0) * Exp_int(2, |s|-1); }
      (if s[|s|-1] == '1' then 1 else 0) * Exp_int(2, |s|-1) + Str2Nat(s[0..|s|-1]);
      { assert Exp_int(2, |s|-1) == 2 * Exp_int(2, |s|-2); }
      (if s[|s|-1] == '1' then 1 else 0) * 2 * Exp_int(2, |s|-2) + Str2Nat(s[0..|s|-1]);
      2 * ((if s[|s|-1] == '1' then 1 else 0) * Exp_int(2, |s|-2)) + Str2Nat(s[0..|s|-1]);
      == { assert (if s[|s|-1] == '1' then 1 else 0) * Exp_int(2, |s|-2) == Str2Nat(s[|s|-1..|s|-1]); }
      2 * Str2Nat(s[|s|-1..|s|-1]) + Str2Nat(s[0..|s|-1]);
    }
  }
}

method AddVerified(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var i := |s1|;
  var j := |s2|;
  var carry := 0;
  res := "";
  
  while i > 0 || j > 0 || carry > 0
    invariant ValidBitString(res)
    invariant carry == 0 || carry == 1
    invariant Str2Int(res) + carry * Exp_int(2, |res|) == Str2Int(s1[0..i]) + Str2Int(s2[0..j])
  {
    var digit1 := if i > 0 then (if s1[i-1] == '1' then 1 else 0) else 0;
    var digit2 := if j > 0 then (if s2[j-1] == '1' then 1 else 0) else 0;
    var sum := digit1 + digit2 + carry;
    var newDigit := sum % 2;
    carry := sum / 2;
    res := (if newDigit == 1 then "1" else "0") + res;
    if i > 0 { i := i - 1; }
    if j > 0 { j := j - 1; }
  }
}

lemma ModExpPow2Lemma(x: nat, pow2_val: nat, n: nat, mod_val: nat)
  requires pow2_val == Exp_int(2, n) || pow2_val == 0
  requires mod_val > 1
  ensures Exp_int(Exp_int(x, pow2_val), 2) % mod_val == Exp_int(x, pow2_val * 2) % mod_val
{
  if pow2_val == 0 {
    calc {
      Exp_int(Exp_int(x, pow2_val), 2) % mod_val;
      Exp_int(Exp_int(x, 0), 2) % mod_val;
      Exp_int(1, 2) % mod_val;
      1 % mod_val;
    }
    calc {
      Exp_int(x, pow2_val * 2) % mod_val;
      Exp_int(x, 0) % mod_val;
      1 % mod_val;
    }
  } else {
    calc {
      pow2_val * 2;
      Exp_int(2, n) * 2;
      Exp_int(2, n+1);
    }
    calc {
      Exp_int(Exp_int(x, pow2_val), 2) % mod_val;
      Exp_int(Exp_int(x, Exp_int(2,n)), 2) % mod_val;
      { assert Exp_int(x, Exp_int(2,n)) * Exp_int(x, Exp_int(2,n)) == Exp_int(x, Exp_int(2,n) + Exp_int(2,n)); }
      Exp_int(x, Exp_int(2,n) * 2) % mod_val;
    }
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
  if n == 0 {
    res := sx; // y is either 1 ("1") or 0 ("0")
    if sy == "0" {
      res := "1"; // x^0 = 1
    }
  } else {
    var inner_res := ModExpPow2(sx, sy[0..|sy|-1], n-1, sz);
    var squared_inner := AddVerified(inner_res, inner_res);
    res := squared_inner;
    var x_int := Str2Int(sx);
    var inner_y_int := Str2Int(sy[0..|sy|-1]);
    var y_val_is_power_of_2 := Str2Int(sy) == Exp_int(2,n);
    var inner_y_val_is_power_of_2_or_0 := (inner_y_int == Exp_int(2,n-1) || inner_y_int == 0);
    
    assert Str2Int(inner_res) == Exp_int(x_int, inner_y_int) % Str2Int(sz);
    Str2IntEqualsStr2Nat(squared_inner);
    assert Str2Int(squared_inner) == 2 * Str2Int(inner_res);
    ModExpPow2Lemma(x_int, inner_y_int, n-1, Str2Int(sz));
    assert (Exp_int(x_int, inner_y_int) % Str2Int(sz)) * 2 % Str2Int(sz) == Exp_int(x_int, inner_y_int * 2) % Str2Int(sz);
    
    calc {
      Str2Int(res);
      Str2Int(squared_inner);
      2 * Str2Int(inner_res);
      2 * (Exp_int(x_int, inner_y_int) % Str2Int(sz));
      2 * (Exp_int(x_int, inner_y_int) % Str2Int(sz)) % Str2Int(sz);
      Exp_int(x_int, inner_y_int * 2) % Str2Int(sz);
      { assert inner_y_int * 2 == Str2Int(sy); }
      Exp_int(x_int, Str2Int(sy)) % Str2Int(sz);
    }
  }
}
// </vc-code>

