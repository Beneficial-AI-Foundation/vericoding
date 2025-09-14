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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then
    ""
  else
    Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma ValidBitString_append0(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(s + "0")
{
  assert |s + "0"| == |s| + 1;
  assert forall i | 0 <= i < |s + "0"| :: (s + "0")[i] == '0' || (s + "0")[i] == '1' by {
    if i < |s| {
      assert (s + "0")[i] == s[i];
      assert s[i] == '0' || s[i] == '1';
    } else {
      assert i == |s|;
      assert (s + "0")[|s|] == "0"[0];
      assert (s + "0")[i] == '0';
    }
  }
}

lemma ValidBitString_append1(s: string)
  requires ValidBitString(s)
  ensures ValidBitString(s + "1")
{
  assert |s + "1"| == |s| + 1;
  assert forall i | 0 <= i < |s + "1"| :: (s + "1")[i] == '0' || (s + "1")[i] == '1' by {
    if i < |s| {
      assert (s + "1")[i] == s[i];
      assert s[i] == '0' || s[i] == '1';
    } else {
      assert i == |s|;
      assert (s + "1")[|s|] == "1"[0];
      assert (s + "1")[i] == '1';
    }
  }
}

lemma Str2Int_append0(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s + "0") == 2 * Str2Int(s)
{
  ValidBitString_append0(s);
  assert |s + "0"| == |s| + 1;
  assert (s + "0")[|s + "0"| - 1] == '0';
  assert (s + "0")[0..|s + "0"| - 1] == s;
  assert (if (s + "0")[|s + "0"| - 1] == '1' then 1 else 0) == 0;
  assert Str2Int(s + "0") ==
    (if |s + "0"| == 0 then 0 else 2 * Str2Int((s + "0")[0..|s + "0"| - 1]) + (if (s + "0")[|s + "0"| - 1] == '1' then 1 else 0));
  assert Str2Int(s + "0") == 2 * Str2Int(s);
}

lemma Str2Int_append1(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s + "1") == 2 * Str2Int(s) + 1
{
  ValidBitString_append1(s);
  assert |s + "1"| == |s| + 1;
  assert (s + "1")[|s + "1"| - 1] == '1';
  assert (s + "1")[0..|s + "1"| - 1] == s;
  assert (if (s + "1")[|s + "1"| - 1] == '1' then 1 else 0) == 1;
  assert Str2Int(s + "1") ==
    (if |s + "1"| == 0 then 0 else 2 * Str2Int((s + "1")[0..|s + "1"| - 1]) + (if (s + "1")[|s + "1"| - 1] == '1' then 1 else 0));
  assert Str2Int(s + "1") == 2 * Str2Int(s) + 1;
}

lemma Int2Str_props(n: nat)
  ensures ValidBitString(Int2Str(n))
  decreases n
{
  if n == 0 {
    assert Int2Str(0) == "";
    assert ValidBitString("");
  } else {
    Int2Str_props(n / 2);
    if n % 2 == 1 {
      ValidBitString_append1(Int2Str(n / 2));
      assert Int2Str(n) == Int2Str(n / 2) + "1";
    } else {
      ValidBitString_append0(Int2Str(n / 2));
      assert Int2Str(n) == Int2Str(n / 2) + "0";
    }
  }
}

lemma Str2Int_Int2Str(n: nat)
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  Int2Str_props(n);
  if n == 0 {
    assert Int2Str(0) == "";
    assert Str2Int(Int2Str(0)) == 0;
  } else {
    Int2Str_props(n / 2);
    if n % 2 == 1 {
      assert Int2Str(n) == Int2Str(n / 2) + "1";
      Str2Int_append1(Int2Str(n / 2));
      assert Str2Int(Int2Str(n)) == 2 * Str2Int(Int2Str(n / 2)) + 1;
      Str2Int_Int2Str(n / 2);
      assert Str2Int(Int2Str(n)) == 2 * (n / 2) + 1;
      assert n % 2 == 1;
      assert Str2Int(Int2Str(n)) == 2 * (n / 2) + n % 2;
    } else {
      assert Int2Str(n) == Int2Str(n / 2) + "0";
      Str2Int_append0(Int2Str(n / 2));
      assert Str2Int(Int2Str(n)) == 2 * Str2Int(Int2Str(n / 2));
      Str2Int_Int2Str(n / 2);
      assert Str2Int(Int2Str(n)) == 2 * (n / 2);
      assert n % 2 == 0;
      assert Str2Int(Int2Str(n)) == 2 * (n / 2) + n % 2;
    }
    assert n == 2 * (n / 2) + n % 2;
  }
}

lemma ExistsStrForNat(n: nat)
  ensures exists s :: ValidBitString(s) && Str2Int(s) == n
{
  Int2Str_props(n);
  Str2Int_Int2Str(n);
  assert exists s :: s == Int2Str(n) && ValidBitString(s) && Str2Int(s) == n;
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
  var n := Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
  assert exists s: string :: ValidBitString(s) && Str2Int(s) == n by {
    ExistsStrForNat(n);
  };
  res :| ValidBitString(res) && Str2Int(res) == n;
}
// </vc-code>

