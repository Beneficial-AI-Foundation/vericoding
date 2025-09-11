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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Str2Int_append(s: string, b: string)
  requires |b| == 1
  requires b[0] == '0' || b[0] == '1'
  ensures Str2Int(s + b) == 2 * Str2Int(s) + (if b[0] == '1' then 1 else 0)
  decreases |s|
{
  // Unfold definition of Str2Int on s + b
  assert Str2Int(s + b) ==
    (if |s + b| == 0 then 0 else 2 * Str2Int((s + b)[0..|s + b| - 1]) + (if (s + b)[|s + b| - 1] == '1' then 1 else 0));
  // |s + b| > 0 because |b| == 1
  assert |s + b| > 0;
  // The prefix (s + b)[0..|s + b|-1] is s, and last char is b[0]
  assert (s + b)[0..|s + b| - 1] == s;
  assert (s + b)[|s + b| - 1] == b[0];
  calc {
    Str2Int(s + b);
    == { }
    2 * Str2Int(s) + (if b[0] == '1' then 1 else 0);
  }
}

lemma Int2Str_correct(n: nat)
  ensures Str2Int(Int2Str(n)) == n
  ensures ValidBitString(Int2Str(n))
  decreases n
{
  if n == 0 {
    // Int2Str(0) == ""
    assert Int2Str(0) == "";
    assert Str2Int(Int2Str(0)) == 0;
    // Empty string vacuously satisfies ValidBitString
    assert ValidBitString(Int2Str(0));
  } else {
    // IH for n/2
    Int2Str_correct(n / 2);
    var s := Int2Str(n / 2);
    var bstr := if n % 2 == 1 then "1" else "0";
    // unfold Int2Str for n
    assert Int2Str(n) == s + bstr;
    // apply append lemma
    Str2Int_append(s, bstr);
    assert Str2Int(Int2Str(n)) == 2 * Str2Int(s) + (if bstr[0] == '1' then 1 else 0);
    // by IH Str2Int(s) == n/2
    assert Str2Int(s) == n / 2;
    // relation between remainder and bit
    assert (if bstr[0] == '1' then 1 else 0) == n % 2;
    // arithmetic identity
    assert 2 * (n / 2) + n % 2 == n;
    assert Str2Int(Int2Str(n)) == n;
    // ValidBitString: s is valid by IH and bstr is a single bit
    assert ValidBitString(s);
    assert bstr[0] == '0' || bstr[0] == '1';
    // show ValidBitString(s + bstr)
    assert ValidBitString(s + bstr);
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
  var gx := Str2Int(sx);
  var gy := Str2Int(sy);
  var gz := Str2Int(sz);
  var r := Exp_int(gx, gy) % gz;
  ghost {
    Int2Str_correct(r);
  }
  res := Int2Str(r);
}
// </vc-code>

