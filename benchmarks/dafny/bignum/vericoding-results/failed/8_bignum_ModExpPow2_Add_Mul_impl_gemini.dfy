// <vc-preamble>
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{

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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [added StringToNat method for non-ghost string to nat conversion] */
method StringToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
    n := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant ValidBitString(s)
        invariant n == Str2Int(s[..i])
        decreases |s| - i
    {
        n := 2 * n;
        if s[i] == '1'
        {
            n := n + 1;
        }
        i := i + 1;
    }
}

lemma SyPrevProps(sy: string, n: nat)
  requires n > 0
  requires ValidBitString(sy) && |sy| == n + 1 && Str2Int(sy) == Exp_int(2, n)
  ensures ValidBitString(sy[0..n])
  ensures |sy[0..n]| == n
  ensures Str2Int(sy[0..n]) == Exp_int(2, n-1)
{
  var sy_prev := sy[0..n];
  var term := if sy[n] == '1' then 1 else 0;
  assert Exp_int(2, n) == 2 * Str2Int(sy_prev) + term;
  assert Exp_int(2, n) % 2 == 0;
  assert term == 0;
  assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
  assert Str2Int(sy_prev) == Exp_int(2, n-1);
}

method NatToString(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
    if n == 0 {
        s := "0";
    } else if n == 1 {
        s := "1";
    } else {
        var prefix := NatToString(n / 2);
        var suffix := if n % 2 == 1 then "1" else "0";
        s := prefix + suffix;
    }
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)

  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [replaced ghost Str2Int with non-ghost StringToNat to fix compilation errors] */
  if n == 0 {
    assert |sy| == 1;
    if sy == "0" { 
      res := "1";
    } else { 
      assert sy == "1";
      var x_val := StringToNat(sx);
      var z_val := StringToNat(sz);
      var mod_val := x_val % z_val;
      res := NatToString(mod_val);
    }
  } else {
    var sy_prev := sy[0..n];
    SyPrevProps(sy, n);
    
    var s_rec := ModExpPow2(sx, sy_prev, n - 1, sz);
    
    var v_rec := StringToNat(s_rec);
    var v_sz := StringToNat(sz);
    var v_res := (v_rec * v_rec) % v_sz;
    
    res := NatToString(v_res);
  }
}
// </vc-code>
