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
function NatToBin(n: nat): string
  ensures ValidBitString(NatToBin(n))
  ensures Str2Int(NatToBin(n)) == n
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else
    var p := NatToBin(n / 2);
    p + (if n % 2 == 1 then "1" else "0")
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
  decreases n
{
  if n == 0 {
    s := "";
    assert |s| == 0;
    assert forall i | 0 <= i < |s| :: s[i] == '0';
    assert ValidBitString(s);
    assert Str2Int(s) == 0;
  } else {
    var pref := Zeros(n - 1);
    s := pref + "0";
    assert |s| == n;
    // the last character of s is '0' and the prefix is pref
    assert s[0..|s|-1] == pref;
    assert s[|s|-1] == '0';
    assert forall i | 0 <= i < |s| :: s[i] == '0';
    assert ValidBitString(s);
    // Str2Int(s) == 2*Str2Int(pref) + 0 by definition of Str2Int
    assert Str2Int(pref) == 0;
    // unfold Str2Int(s) via its definition
    if |s| == 0 {
      assert Str2Int(s) == 0;
    } else {
      assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      assert Str2Int(s) == 2 * Str2Int(pref) + 0;
      assert Str2Int(s) == 0;
    }
  }
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
  if n == 0 {
    if Str2Int(sy) == 0 {
      // exponent 0 -> result 1 mod sz
      res := NatToBin(1 % Str2Int(sz));
    } else {
      // exponent 1 -> sx mod sz
      res := NatToBin(Str2Int(sx) % Str2Int(sz));
    }
  } else {
    // compute value for half exponent (2^(n-1) or 0)
    var syPref := sy[0..|sy|-1];
    var half := ModExpPow2(sx, syPref, n - 1, sz);
    var a := Str2Int(half);
    var m := Str2Int(sz);
    var sqv := (a * a) % m;
    if Str2Int(sy) == 0 {
      res := NatToBin(1 % m);
    } else {
      res := NatToBin(sqv);
    }
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
  // Recursive binary-exponentiation on the bitstring exponent sy.
  if |sy| == 1 {
    if sy[0] == '0' {
      // exponent 0 -> 1 mod sz
      res := NatToBin(1 % Str2Int(sz));
      return;
    } else {
      // exponent 1 -> sx mod sz
      res := NatToBin(Str2Int(sx) % Str2Int(sz));
      return;
    }
  } else {
    var pref := sy[0..|sy|-1];
    var last := sy[|sy|-1];
    var t := ModExp(sx, pref, sz); // computes sx^(prefix) mod sz
    var tv := Str2Int(t);
    var m := Str2Int(sz);
    var squared := (tv * tv) % m;
    if last == '1' {
      var resv := (squared * Str2Int(sx)) % m;
      res := NatToBin(resv);
      return;
    } else {
      res := NatToBin(squared);
      return;
    }
  }
}
// </vc-code>

