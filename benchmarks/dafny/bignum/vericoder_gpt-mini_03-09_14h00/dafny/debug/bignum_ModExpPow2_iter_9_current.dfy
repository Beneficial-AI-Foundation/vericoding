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
ghost function Int2Str(v: nat): string
  decreases v
{
  if v == 0 then "" else Int2Str(v / 2) + (if v % 2 == 1 then "1" else "0")
}

lemma Int2Str_props(v: nat)
  ensures ValidBitString(Int2Str(v))
  ensures Str2Int(Int2Str(v)) == v
  decreases v
{
  if v == 0 {
    assert Int2Str(v) == "";
    assert ValidBitString(Int2Str(v));
    assert Str2Int(Int2Str(v)) == 0;
  } else {
    Int2Str_props(v / 2);
    var p := Int2Str(v / 2);
    var c := (if v % 2 == 1 then "1" else "0");
    var s := p + c;
    assert Int2Str(v) == s;
    // Prove ValidBitString(s)
    assert forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
    {
      if i < |p| {
        assert s[i] == p[i];
        assert p[i] == '0' || p[i] == '1';
      } else {
        assert i == |p|;
        assert s[i] == c[0];
        if v % 2 == 1 {
          assert c[0] == '1';
        } else {
          assert c[0] == '0';
        }
      }
    }
    assert ValidBitString(s);
    // Prove Str2Int(s) == v
    assert Str2Int(p) == v / 2;
    assert Str2Int(s) == 2 * Str2Int(p) + (if s[|s|-1] == '1' then 1 else 0);
    if v % 2 == 1 {
      assert s[|s|-1] == '1';
      assert Str2Int(s) == 2 * (v / 2) + 1;
    } else {
      assert s[|s|-1] == '0';
      assert Str2Int(s) == 2 * (v / 2) + 0;
    }
    assert 2 * (v / 2) + (if v % 2 == 1 then 1 else 0) == v;
    assert Str2Int(s) == v;
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
  var m := Str2Int(sz);
  var e := Str2Int(sy);
  if e == 0 {
    res := Int2Str(1 % m);
    Int2Str_props(1 % m);
    return;
  }
  assert e == Exp_int(2, n);
  var r := Str2Int(sx) % m;
  var i := 0;
  assert r == Exp_int(Str2Int(sx), Exp_int(2, 0)) % m;
  while i < n
    invariant 0 <= i <= n
    invariant r < m
    invariant r == Exp_int(Str2Int(sx), Exp_int(2, i)) % m
    decreases n - i
  {
    var oldi := i;
    var oldr := r;
    var base := Str2Int(sx);
    var t := Exp_int(2, oldi);
    var a := Exp_int(base, t);
    assert oldr == a % m;
    r := (r * r) % m;
    assert r == (oldr * oldr) % m;
    Mod_mul_mod(a, m);
    assert r == (a * a) % m;
    Exp_int_mul(base, t, t);
    assert (a * a) % m == Exp_int(base, t + t) % m;
    Exp2_succ(oldi);
    assert t + t == Exp_int(2, oldi + 1);
    assert r == Exp_int(base, Exp_int(2, oldi + 1)) % m;
    i := i + 1;
  }
  res := Int2Str(r);
  Int2Str_props(r);
}
// </vc-code>

