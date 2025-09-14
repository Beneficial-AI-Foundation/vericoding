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

// <vc-helpers>
ghost function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma lemma_ValidBitString_append_bit(s: string, b: bool)
  requires ValidBitString(s)
  ensures ValidBitString(s + (if b then "1" else "0"))
{
  assert |s + (if b then "1" else "0")| == |s| + 1;
  assert forall i | 0 <= i < |s| :: (s + (if b then "1" else "0"))[i] == s[i];
  assert (s + (if b then "1" else "0"))[|s|] == (if b then '1' else '0');

  assert forall i | 0 <= i < |s + (if b then "1" else "0")| ::
    (s + (if b then "1" else "0"))[i] == '0' || (s + (if b then "1" else "0"))[i] == '1' by {
      if i < |s| {
        assert (s + (if b then "1" else "0"))[i] == s[i];
      } else {
        assert i == |s|;
        if b {
          assert (s + "1")[i] == '1';
        } else {
          assert (s + "0")[i] == '0';
        }
      }
    }
}

lemma lemma_Str2Int_appendBit(s: string, b: bool)
  requires ValidBitString(s)
  ensures ValidBitString(s + (if b then "1" else "0"))
  ensures Str2Int(s + (if b then "1" else "0")) == 2 * Str2Int(s) + (if b then 1 else 0)
{
  lemma_ValidBitString_append_bit(s, b);
  var t := s + (if b then "1" else "0");
  assert |t| == |s| + 1;
  assert t[0..|s|] == s;
  assert |t| - 1 == |s|;
  assert t[0..|t|-1] == s;
  if b {
    assert t[|t|-1] == '1';
  } else {
    assert t[|t|-1] == '0';
  }
  reveal Str2Int();
  assert |t| > 0;
  assert Str2Int(t) == 2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
  if b {
    assert (if t[|t|-1] == '1' then 1 else 0) == 1;
  } else {
    assert (if t[|t|-1] == '1' then 1 else 0) == 0;
  }
}

lemma lemma_Int2Str_Correct(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 {
    assert ValidBitString("");
    reveal Str2Int();
    assert Str2Int("") == 0;
  } else {
    lemma_Int2Str_Correct(n / 2);
    reveal Int2Str();
    var s := Int2Str(n / 2);
    var b := n % 2 == 1;
    assert Int2Str(n) == s + (if b then "1" else "0");
    lemma_Str2Int_appendBit(s, b);
    assert Str2Int(Int2Str(n)) == 2 * Str2Int(s) + (if b then 1 else 0);
    assert Str2Int(s) == n / 2;
    assert (if b then 1 else 0) == n % 2;
    assert 2 * (n / 2) + (n % 2) == n;
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
ghost function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma lemma_ValidBitString_append_bit(s: string, b: bool)
  requires ValidBitString(s)
  ensures ValidBitString(s + (if b then "1" else "0"))
{
  assert |s + (if b then "1" else "0")| == |s| + 1;
  assert forall i | 0 <= i < |s| :: (s + (if b then "1" else "0"))[i] == s[i];
  assert (s + (if b then "1" else "0"))[|s|] == (if b then '1' else '0');

  assert forall i | 0 <= i < |s + (if b then "1" else "0")| ::
    (s + (if b then "1" else "0"))[i] == '0' || (s + (if b then "1" else "0"))[i] == '1' by {
      if i < |s| {
        assert (s + (if b then "1" else "0"))[i] == s[i];
      } else {
        assert i == |s|;
        if b {
          assert (s + "1")[i] == '1';
        } else {
          assert (s + "0")[i] == '0';
        }
      }
    }
}

lemma lemma_Str2Int_appendBit(s: string, b: bool)
  requires ValidBitString(s)
  ensures ValidBitString(s + (if b then "1" else "0"))
  ensures Str2Int(s + (if b then "1" else "0")) == 2 * Str2Int(s) + (if b then 1 else 0)
{
  lemma_ValidBitString_append_bit(s, b);
  var t := s + (if b then "1" else "0");
  assert |t| == |s| + 1;
  assert t[0..|s|] == s;
  assert |t| - 1 == |s|;
  assert t[0..|t|-1] == s;
  if b {
    assert t[|t|-1] == '1';
  } else {
    assert t[|t|-1] == '0';
  }
  reveal Str2Int();
  assert |t| > 0;
  assert Str2Int(t) == 2 * Str2Int(t[0..|t|-1]) + (if t[|t|-1] == '1' then 1 else 0);
  if b {
    assert (if t[|t|-1] == '1' then 1 else 0) == 1;
  } else {
    assert (if t[|t|-1] == '1' then 1 else 0) == 0;
  }
}

lemma lemma_Int2Str_Correct(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 {
    assert ValidBitString("");
    reveal Str2Int();
    assert Str2Int("") == 0;
  } else {
    lemma_Int2Str_Correct(n / 2);
    reveal Int2Str();
    var s := Int2Str(n / 2);
    var b := n % 2 == 1;
    assert Int2Str(n) == s + (if b then "1" else "0");
    lemma_Str2Int_appendBit(s, b);
    assert Str2Int(Int2Str(n)) == 2 * Str2Int(s) + (if b then 1 else 0);
    assert Str2Int(s) == n / 2;
    assert (if b then 1 else 0) == n % 2;
    assert 2 * (n / 2) + (n % 2) == n;
  }
// </vc-code>

