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
lemma {:induction s, t} LemmaStr2IntConcat(s: string, t: string)
  requires ValidBitString(s) && ValidBitString(t)
  ensures Str2Int(s + t) == Str2Int(s) * Exp_int(2, |t|) + Str2Int(t)
  decreases |s|
{
  if |s| == 0 {
    assert s + t == t;
  } else {
    var s' := s[0..|s|-1];
    var last_char := s[|s|-1];
    LemmaStr2IntConcat(s', t);
    assert s + t == (s' + [last_char]) + t == s' + ([last_char] + t);
    assert Str2Int(s) == 2 * Str2Int(s') + (if last_char == '1' then 1 else 0);
    assert |[last_char] + t| == |t| + 1;
    calc {
      Str2Int(s + t);
      == Str2Int(s' + ([last_char] + t));
      == {LemmaStr2IntConcat(s', [last_char] + t);} 
         Str2Int(s') * Exp_int(2, |[last_char] + t|) + Str2Int([last_char] + t);
      == Str2Int(s') * Exp_int(2, |t| + 1) + Str2Int([last_char] + t);
      == 2 * Str2Int(s') * Exp_int(2, |t|) + Str2Int([last_char] + t);
      == {assert Str2Int([last_char] + t) == 2 * Str2Int(t) + (if last_char == '1' then 1 else 0);}
         2 * Str2Int(s') * Exp_int(2, |t|) + (2 * Str2Int(t) + (if last_char == '1' then 1 else 0));
      == 2 * (Str2Int(s') * Exp_int(2, |t|) + Str2Int(t)) + (if last_char == '1' then 1 else 0);
      == {LemmaStr2IntConcat(s', t);} 
         2 * Str2Int(s' + t) + (if last_char == '1' then 1 else 0);
      == {assert s' + t == s[0..|s|-1] + t;}
         Str2Int(s);
    }
  }
}

function Int2Str(n: nat, len: nat): string
  requires n < Exp_int(2, len)
  ensures ValidBitString(Int2Str(n, len))
  ensures Str2Int(Int2Str(n, len)) == n
{
  if len == 0 then
    ""
  else
    Int2Str(n / 2, len - 1) + (if n % 2 == 1 then "1" else "0")
}

lemma Int2StrProperties(n: nat, len: nat)
  requires n < Exp_int(2, len)
  ensures ValidBitString(Int2Str(n, len))
  ensures Str2Int(Int2Str(n, len)) == n
  decreases len
{
  if len > 0 {
    Int2StrProperties(n / 2, len - 1);
    assert n / 2 < Exp_int(2, len - 1);
    assert (n % 2) < 2;
  }
}

ghost function Str2IntSingleChar(c: char): nat 
  requires c == '0' || c == '1'
  ensures Str2Int([c]) == (if c == '1' then 1 else 0)
{
  if c == '1' then 1 else 0
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
  var x_int := Str2Int(sx);
  var z_int := Str2Int(sz);
  var L := |sz|;
  
  if |sy| == 1 {
    if sy[0] == '0' {
      var one_mod_z: nat := 1 % z_int;
      Int2StrProperties(one_mod_z, L);
      res := Int2Str(one_mod_z, L);
    } else {
      assert sy[0] == '1';
      var x_mod_z: nat := x_int % z_int;
      Int2StrProperties(x_mod_z, L);
      res := Int2Str(x_mod_z, L);
    }
  } else {
    var sy' := sy[0..|sy|-1];
    var y_last := sy[|sy|-1];
    var half := ModExp(sx, sy', sz);
    var half_int := Str2Int(half);
    var half_squared: nat := half_int * half_int;
    var half_squared_z: nat := half_squared % z_int;
    Int2StrProperties(half_squared_z, L);
    var temp: string := Int2Str(half_squared_z, L);
    
    if y_last == '0' {
      res := temp;
    } else {
      var x_mod_z: nat := x_int % z_int;
      var product: nat := Str2Int(temp) * x_mod_z;
      var final_val: nat := product % z_int;
      Int2StrProperties(final_val, L);
      res := Int2Str(final_val, L);
    }
  }
}
// </vc-code>

