```vc-helpers
method ParseBits(s: string) returns (v: nat)
  requires ValidBitString(s)
  ensures v == Str2Int(s)
  ensures v < Exp_int(2, |s|)
  decreases |s|
{
  if |s| == 0 {
    v := 0;
  } else {
    var prefix := s[0..|s|-1];
    var pv := ParseBits(prefix);
    var bit := if s[|s|-1] == '1' then 1 else 0;
    v := 2 * pv + bit;
  }
}

method BuildBinary(n: nat, v: nat) returns (s: string)
  requires v < Exp_int(2, n)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == v
  decreases n
{
  if n == 0 {
    s := "";
  } else {
    var low := v % 2;
    var high := v / 2;
    var rest := BuildBinary(n - 1, high);
    s := rest + (if low == 1 then "1" else "0");
  }
}

lemma ExpInt_add(a: nat, n: nat, m: nat)
  ensures Exp_int(a, n + m) == Exp_int(a, n) * Exp_int(a, m)
  decreases m
{
  if m == 0 {
  } else {
    ExpInt_add(a, n, m - 1);
    // Exp_int(a, n + m) = a * Exp_int(a, n + m - 1)
    assert Exp_int(a, n + m) == a * Exp_int(a, n + m - 1);
    // By IH Exp_int(a, n + m - 1) == Exp_int(a, n) * Exp_int(a, m - 1)
    assert Exp_int(a, n + m - 1) == Exp_int(a, n) * Exp_int(a, m - 1);
    // Hence Exp_int(a, n + m) == a * (Exp_int(a, n) * Exp_int(a, m - 1))
    assert Exp_int(a, n + m) == a * (Exp_int(a, n) * Exp_int(a, m - 1));
    // Rearranging: a * (Exp_int