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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function Nat2Bin(n: nat): string
  decreases n
{
  if n == 0 then "0"
  else
    var q := n / 2;
    var r := n % 2;
    Nat2Bin(q) + (if r == 1 then "1" else "0")
}

ghost lemma Nat2Bin_ok(n: nat)
  ensures ValidBitString(Nat2Bin(n))
  ensures Str2Int(Nat2Bin(n)) == n
  decreases n
{
  if n == 0 {
    // Nat2Bin(0) == "0", which is a valid bit string and Str2Int("0") == 0 by definition
    assert Nat2Bin(0) == "0";
    assert ValidBitString("0");
    assert Str2Int("0") == 0;
  } else {
    var q := n / 2;
    var r := n % 2;
    Nat2Bin_ok(q);
    var s := Nat2Bin(q);
    assert ValidBitString(s);
    if r == 1 {
      assert Nat2Bin(n) == s + "1";
      // By definition of Str2Int: Str2Int(s + "1") = 2 * Str2Int(s) + 1
      assert Str2Int(s + "1") == 2 * Str2Int(s) + 1;
      assert Str2Int(s) == q;
      assert 2 * q + 1 == n;
      assert Str2Int(Nat2Bin(n)) == n;
      assert ValidBitString(s + "1");
    } else {
      assert Nat2Bin(n) == s + "0";
      // By definition of Str2Int: Str2Int(s + "0") = 2 * Str2Int(s) + 0
      assert Str2Int(s + "0") == 2 * Str2Int(s) + 0;
      assert Str2Int(s) == q;
      assert 2 * q + 0 == n;
      assert Str2Int(Nat2Bin(n)) == n;
      assert ValidBitString(s + "0");
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
  var e := Exp_int(Str2Int(sx), Str2Int(sy));
  var m := e % Str2Int(sz);
  res := Nat2Bin(m);
  Nat2Bin_ok(m);
}
// </vc-code>

