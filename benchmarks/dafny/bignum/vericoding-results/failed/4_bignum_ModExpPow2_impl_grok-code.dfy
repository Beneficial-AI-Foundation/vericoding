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
function Int2Str(v: nat): string
  decreases v
{
  if v == 0 then "0"
  else Int2Str(v / 2) + (if v % 2 == 1 then "1" else "0")
}

function StrToInt(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * StrToInt(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

function MulBig(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
{
  Int2Str(StrToInt(s1) * StrToInt(s2))
}

function ModBig(s: string, m: string): string
  requires ValidBitString(s) && ValidBitString(m) && StrToInt(m) > 0
{
  Int2Str(StrToInt(s) % StrToInt(m))
}

lemma Str2Int_Equals_StrToInt(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == StrToInt(s)
  decreases s
{
  if |s| == 0 {
  } else {
    Str2Int_Equals_StrToInt(s[0..|s|-1]);
  }
}

// Fix: Add lemma to establish that Int2Str produces a valid bit string
lemma Int2Str_IsValid(v: nat)
  ensures ValidBitString(Int2Str(v))
  decreases v
{
  if v == 0 {
  } else {
    Int2Str_IsValid(v / 2);
  }
}

lemma ModBig_Valid(s: string, m: string)
  requires ValidBitString(s) && ValidBitString(m) && StrToInt(m) > 0
  ensures ValidBitString(ModBig(s, m))
{
  var v := StrToInt(s) % StrToInt(m);
  Int2Str_IsValid(v);
  assert Str2Int(ModBig(s, m)) == v by {
    Str2Int_Equals_StrToInt(ModBig(s, m));
  }
}

lemma MulBig_Valid(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(MulBig(s1, s2))
{
  var v := StrToInt(s1) * StrToInt(s2);
  Int2Str_IsValid(v);
  assert Str2Int(MulBig(s1, s2)) == v by {
    Str2Int_Equals_StrToInt(MulBig(s1, s2));
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
  var isZero := true;
  for i := 0 to |sy|-1
    invariant 0 <= i <= |sy|
  {
    if sy[i] == '1' {
      isZero := false;
      break;
    }
  }
  if isZero {
    res := "1";
    Int2Str_IsValid(1);
  } else {
    var acc: string := ModBig(sx, sz);
    ModBig_Valid(sx, sz);
    var i: nat := 0;
    while i < n
      invariant 0 <= i <= n
      invariant ValidBitString(acc)
      invariant Str2Int(acc) == Exp_int(Str2Int(sx), Exp_int(2, i)) % Str2Int(sz)
      decreases n - i
    {
      var temp := MulBig(acc, acc);
      MulBig_Valid(acc, acc);
      var new_acc := ModBig(temp, sz);
      ModBig_Valid(temp, sz);
      acc := new_acc;
      i := i + 1;
    }
    res := acc;
    Int2Str_IsValid(Str2Int(res));
  }
}
// </vc-code>

