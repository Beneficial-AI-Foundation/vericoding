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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
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
lemma TwiceLemma(s: string)
  requires ValidBitString(s)
  ensures 2 * Str2Int(s) == Str2Int(s + "0")
  decreases s
{
  if |s| == 0 {
    assert s + "0" == "0";
    assert Str2Int(s + "0") == 0;
  } else {
    TwiceLemma(s[0..|s|-1]);
    var c: char := s[|s|-1];
    assert s + "0" == (s[0..|s|-1] + ToString(c)) + "0";
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if c == '1' then 1 else 0);
    assert Str2Int(s + "0") == 2 * Str2Int(s) + (if '0' == '1' then 1 else 0);
    assert Str2Int(s + "0") == 2 * Str2Int(s) + 0;
  }
}

lemma AddOneLemma(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s + "1") == 2 * Str2Int(s) + 1
  decreases s
{
  if |s| == 0 {
    assert s + "1" == "1";
    assert Str2Int("1") == 1;
  } else {
    AddOneLemma(s[0..|s|-1]);
    var c: char := s[|s|-1];
    assert s + "1" == (s[0..|s|-1] + ToString(c)) + "1";
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if c == '1' then 1 else 0);
    assert Str2Int(s + "1") == 2 * Str2Int(s) + (if '1' == '1' then 1 else 0);
    assert Str2Int(s + "1") == 2 * Str2Int(s) + 1;
  }
}

lemma PowLemma(x: nat, y: nat)
  ensures Exp_int(x, y) == (if y == 0 then 1 else Exp_int(x, y - 1) * x)
{
}

lemma ModExpLemma(a: nat, b: nat, m: nat)
  requires m > 1
  ensures Exp_int(a, b) % m == (if b == 0 then 1 % m else (a * (Exp_int(a, b - 1) % m)) % m)
{
  if b == 0 {
    assert Exp_int(a, b) == 1;
  } else {
    PowLemma(a, b);
    assert Exp_int(a, b) == a * Exp_int(a, b - 1);
    calc {
      (a * Exp_int(a, b - 1)) % m;
      ==
      (a * ((Exp_int(a, b - 1) % m) + m * (Exp_int(a, b - 1) / m))) % m;
      ==
      (a * (Exp_int(a, b - 1) % m) + a * m * (Exp_int(a, b - 1) / m)) % m;
      ==
      { assert (a * m * (Exp_int(a, b - 1) / m)) % m == 0; }
      (a * (Exp_int(a, b - 1) % m)) % m;
    }
  }
}

function ToString(c: char): string
{
  [c]
}

lemma ExpIntSplit(x: nat, y1: nat, y2: nat)
  ensures Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2)
{
  if y2 == 0 {
    assert Exp_int(x, y1 + 0) == Exp_int(x, y1);
    assert Exp_int(x, 0) == 1;
  } else {
    ExpIntSplit(x, y1, y2 - 1);
    assert Exp_int(x, y1 + y2) == x * Exp_int(x, y1 + y2 - 1);
    assert Exp_int(x, y1) * Exp_int(x, y2) == Exp_int(x, y1) * (x * Exp_int(x, y2 - 1));
    assert Exp_int(x, y1) * (x * Exp_int(x, y2 - 1)) == x * (Exp_int(x, y1) * Exp_int(x, y2 - 1));
  }
}

lemma ModExpLemma2(a: nat, b: nat, m: nat)
  requires m > 1
  ensures Exp_int(a, b) % m == (if b == 0 then 1 % m else (a * (Exp_int(a, b - 1) % m)) % m)
{
  ModExpLemma(a, b, m);
}

lemma ExpIntSplit2(x: nat, y1: nat, y2: nat)
  ensures Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2)
{
  ExpIntSplit(x, y1, y2);
}

lemma ModExpRecursiveLemma(a: nat, b: nat, m: nat)
  requires m > 1
  ensures Exp_int(a, b) % m == (if b == 0 then 1 % m else 
      let half := Exp_int(a, b/2) % m in
      let square := (half * half) % m in
      if b % 2 == 0 then square else (a * square) % m)
{
  if b == 0 {
    assert Exp_int(a, b) == 1;
  } else {
    var half_b := b/2;
    var rem := b % 2;
    assert b == 2 * half_b + rem;
    ExpIntSplit(a, half_b, half_b);
    assert Exp_int(a, 2 * half_b) == Exp_int(a, half_b) * Exp_int(a, half_b);
    if rem == 0 {
      assert Exp_int(a, b) == Exp_int(a, 2 * half_b);
    } else {
      assert Exp_int(a, b) == a * Exp_int(a, 2 * half_b);
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
  if |sy| == 1 {
    if sy == "0" {
      var zeros := Zeros(|sz|);
      res := zeros;
      assert Str2Int(res) == 0;
      assert Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz) == Exp_int(Str2Int(sx), 0) % Str2Int(sz);
      assert Exp_int(Str2Int(sx), 0) == 1;
      assert 1 % Str2Int(sz) == 1;
    } else {
      var q: string, r: string;
      q, r := DivMod(sx, sz);
      res := r;
      assert Str2Int(res) == Str2Int(sx) % Str2Int(sz);
      assert Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz) == Exp_int(Str2Int(sx), 1) % Str2Int(sz);
      assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    }
  } else {
    var rest := sy[0..|sy|-1];
    var res_rec := ModExp(sx, rest, sz);
    
    var last_char: char := sy[|sy|-1];
    var res_sq := res_rec + "0";
    TwiceLemma(res_rec);
    assert Str2Int(res_sq) == 2 * Str2Int(res_rec);
    
    var q1: string, r1: string;
    q1, r1 := DivMod(res_sq, sz);
    assert Str2Int(r1) == (2 * Str2Int(res_rec)) % Str2Int(sz);
    
    if last_char == '0' {
      res := r1;
      assert Str2Int(res) == (2 * Str2Int(res_rec)) % Str2Int(sz);
      assert Str2Int(res_rec) == Exp_int(Str2Int(sx), Str2Int(rest)) % Str2Int(sz);
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Str2Int(sx), Str2Int(rest) * 2);
      ExpIntSplit(Str2Int(sx), Str2Int(rest), Str2Int(rest));
      assert Exp_int(Str2Int(sx), Str2Int(rest) * 2) == Exp_int(Str2Int(sx), Str2Int(rest)) * Exp_int(Str2Int(sx), Str2Int(rest));
      assert Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz) == (Exp_int(Str2Int(sx), Str2Int(rest)) * Exp_int(Str2Int(sx), Str2Int(rest))) % Str2Int(sz);
    } else {
      var res_sq_x := r1;
      assert Str2Int(res_sq_x) == (2 * Str2Int(res_rec)) % Str2Int(sz);
      
      var res_times_x := res_sq_x + "0";
      TwiceLemma(res_sq_x);
      assert Str2Int(res_times_x) == 2 * Str2Int(res_sq_x);
      
      var q2: string, r2: string;
      q2, r2 := DivMod(res_times_x, sz);
      assert Str2Int(r2) == (2 * Str2Int(res_sq_x)) % Str2Int(sz);
      
      res := r2;
      assert Str2Int(res) == (2 * Str2Int(res_sq_x)) % Str2Int(sz);
      assert Str2Int(res_sq_x) == (2 * Str2Int(res_rec)) % Str2Int(sz);
      assert Str2Int(res_rec) == Exp_int(Str2Int(sx), Str2Int(rest)) % Str2Int(sz);
      assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(Str2Int(sx), Str2Int(rest) * 2 + 1);
      ExpIntSplit(Str2Int(sx), Str2Int(rest) * 2, 1);
      assert Exp_int(Str2Int(sx), Str2Int(rest) * 2 + 1) == Exp_int(Str2Int(sx), Str2Int(rest) * 2) * Str2Int(sx);
      ExpIntSplit(Str2Int(sx), Str2Int(rest), Str2Int(rest));
      assert Exp_int(Str2Int(sx), Str2Int(rest) * 2) == Exp_int(Str2Int(sx), Str2Int(rest)) * Exp_int(Str2Int(sx), Str2Int(rest));
      assert Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz) == (Str2Int(sx) * (Exp_int(Str2Int(sx), Str2Int(rest)) * Exp_int(Str2Int(sx), Str2Int(rest)))) % Str2Int(sz);
    }
  }
}
// </vc-code>

