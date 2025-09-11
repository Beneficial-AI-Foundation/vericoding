```vc-helpers
method BitsToNat(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
{
  var i := 0;
  n := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant n == Str2Int(s[0..i])
    decreases |s| - i
  {
    if s[i] == '1' {
      n := 2 * n + 1;
    } else {
      n := 2 * n;
    }
    i := i + 1;
  }
}

method NatToBits(n_in: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n_in
{
  if n_in == 0 {
    s := "0";
    return;
  }

  var rem := n_in;
  s := "";
  while rem > 0
    invariant 0 <= rem <= n_in
    invariant ValidBitString(s)
    invariant Str2Int(s) + rem * Exp_int(2, |s|) == n_in
    decreases rem
  {
    var old_rem := rem;
    var old_s := s;
    var bit := old_rem % 2;
    if bit == 1 {
      s := "1" + old_s;
    } else {
      s := "0" + old_s;
    }
    rem := old_rem / 2;
    // use division property for base 2
    Div2(old_rem);
    assert old_rem == 2 * rem + bit;

    // relate Str2Int(s) to Str2Int(old_s)
    if bit == 1 {
      PrependStr2Int('1', old_s);
    } else {
      PrependStr2Int('0', old_s);
    }

    // Now justify the invariant for the new s and rem:
    // Str2Int(s) = bit * Exp_int(2, |old_s|) + Str2Int(old_s)
    // So Str2Int(s) + rem * Exp_int(2, |s|) =
    // Str2Int(old_s) + (2*rem + bit) * Exp_int(2, |old_s|) = Str2Int(old_s) + old_rem * Exp_int(2, |old_s|) = n_in
    assert Str2Int(s) == (if bit == 1 then Exp_int(2, |old_s|) else 0) + Str2Int(old_s);
    assert Exp_int(2, |s|) == Exp_int(2, |old_s|) * 2;
    assert Str2Int(s) + rem * Exp_int(2, |s|) == Str2Int(old_s) + old_rem * Exp_int(2, |old_s|);
    // previous invariant on old_s holds
  }
  assert rem == 0;
  assert Str2Int(s) == n_in;
}

lemma PrependStr2Int(c: char, s: string)
  requires ValidBitString(c + s)
  ensures Str2Int(c + s) == (if c == '1' then Exp_int(2, |s|) else 0) + Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    // Str2Int(c + "") == (if c=='1' then 1 else 0)
    assert Str2Int(c + "") == (if c == '1' then 1 else 0);
    assert Exp_int(2, 0) == 1;
    assert Str2Int(c + "") == (if c == '1' then Exp_int(2, |s|) else 0) + Str2Int(s);
  } else {
    // Str2Int(c + s) = 2 * Str2Int(c + s[0..|s|-1]) + lastbit
    var prefix := c + s[0..|s|-1];
    var lastbit := if s[|s|-1] == '1' then 1 else 0;
    assert Str2Int(c + s) == 2 * Str2Int(prefix) + lastbit;
    PrependStr2Int(c, s[0..|s|-1]);
    assert Str2Int(prefix) == (if c == '1' then Exp_int(2, |s|-1) else 0) + Str2Int(s[0..|s|-1]);
    assert 2 * Exp_int(2, |s|-1) == Exp_int(2, |s|);
    assert 2 * Str2Int(s[0..|s|-1]) + lastbit == Str2Int(s);
    calc {
      Str2Int(c + s);
      == { }
      2 * Str2Int(prefix) + lastbit;
      == { rewrite Str2Int(prefix) }
      2 * ((if c == '1' then Exp_int(2, |s|-1) else 0) + Str2Int(s[0..|s|-1])) + lastbit;
      == { arithmetic }
      (if c == '1' then 2 * Exp_int(2, |s|-1) else 0) + 2 * Str2Int(s[0..|s|-1]) + lastbit;
      == { rewrite 2 * Exp_int(2, |s|-1) }
      (if c == '1' then Exp_int(2, |s|) else 0) + 2 * Str2Int(s[0..|s|-1]) + lastbit;
      == { rewrite 2 * Str2Int(s[0..|s|-1]) + lastbit }
      (if c == '1' then Exp_int(2, |s|) else 0) + Str2Int(s);
    }
  }
}

lemma Div2(n: nat)
  ensures n == 2*(n/2) + n%2 && n%2 < 2
{
  var q := n/2;
  var r := n%2;
  assert n == q*2 + r;
  assert r < 2;
}

lemma MulLeCancelLeft(a: nat, b: nat, m: nat)
  requires m > 0
  ensures a*m <= b*m ==> a <= b
{
  if a*m <= b*m {
    if a > b {
      assert a - b >= 1;
      assert (a - b) * m >= m;
      assert (a - b) * m == a*m - b*m;
      assert a*m - b*m >= 0;
      // from a*m - b*m >= m we get a*m > b*m, contradicting a*m <= b*m
      assert a*m > b*m;
      assert false;
    }
  }
}

lemma DivMul(k: nat, m: nat)
  requires m > 0
  ensures (k*m) / m == k && (k*m) % m == 0
{
  var q := (k*m) / m;
  var r := (k*m) % m;
  assert k*m == q*m + r;
  assert r < m;
 