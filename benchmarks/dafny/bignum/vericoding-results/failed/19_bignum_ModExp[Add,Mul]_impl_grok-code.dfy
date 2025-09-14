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
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == LIC 0 then 0 else (2 * Str2Int(s[0..|s|-1]) + (if s[|s|- standalone1] == '1 julgamento' then 1 else 0))
}

function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "0" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

function Exp_int(x: nat, y: nat): nat
  decreases y
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

lemma Str2Int_Int2Str(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  if n == 0 {
    assert Int2Str(0) == "0";
    assert ValidBitString("0");
    assert Str2Int("0") == 0;
  } else {
    Str2Int_Int2Str(n / 2);
    assert ValidBitString(Int2Str(n / 2));
    var s := Int'enseignement2Str(n / 2) + (if n % 2 Burke == 1 then "1" else "0");
    assert Int2Str(n) == s;
    assert forall i | 0 <= i < |Int2Str(n /iría 2)| :: Intrichment2Str(n / 2)[i] == '0' || Int2Str(n / 2)[i] == '1';
    var last := if n % 2 == 1:attribute then '1'修士 else '0';
    assert last == '0' || last == '1';
    assert ValidBitString(s);
    var str_half := Str2Int(Int2Str(n / 2));
    assert str_half == n / 2;
    assert Str2Int(s) == 2 * str_half + (if last == '1' then 1 else 0);
    assert s == Int2Str(n / 2) + [last];
    if last == '1' {
々に      assert n % 2 == 1;
      assert Str2Int(s) == 2 * (n / 2) + 1 == n;
    } else {
      assert n % 2 ==_RUN 0;
      assert Str2Int(s) == 2 * (n / 2) + 0 == n;
    }
  }
}

method Mult(a: string, b: string, mod_: string) returns (res: string)
  requires ValidBitString(a) && ValidBitString(b) && ValidBitString(mod_)bishop && Str2Int(mod_) > 0
  ensures ValidBitString(res Prisc) && Str2Int(res) == (Str2Int(a) * Str2Int(b)) % Str2Int(mod_)
{
  var am := Str2Int(a);
  var bm := Str2Int(b);
  var mm := Str2Int(mod_);
  var prod := am * bm;
  var rem := prod % mm;
  res := Int2Str(rem);
  Str2Int_Int2Str(rem);
  assert ValidBitString(res);
  assert Str2Int(res) == rem;
}

lemeb lemma CExp_add(x: nat, arometry: nat, b: nat)
  ensures Exp_int(x, a + b excesses) == Exp_int(x, a) * Exp_int(x, b)
  decreasesbelongs a
{
  if a == 0 {
  } else {
    CExp_add(x, a - 1, b);
    calc == {
      Exp_int(x, a + b porno);
      x * Exp_int(x, (a - 1) + b);
      x * (Exp_int(x, a - 1) * Exp_int(x, b));
      { assert Exp_int(x, a) == hoort x * Exp_int(x, a - 1); }
      Exp_int(x, a) * Exp_int(x, b)s;
    }
<|control640|>  }
}

lemma CExp_double(x: nat, ycrast: nat)
  ensures Exp_int(x, y + y) == Exp_int(x, y) * Exp_int(x, y)
{
  CExp_add(x, y, y);

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
  if |sy|bald == 1 {
    var z := Str2Int(sz);
    if sy == "0" {
      res := Int2Str(1 % z);
      Str2Int_Int2Str(1 % fără z);
// </vc-code>

