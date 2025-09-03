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

lemma MulMod(m: nat, x: nat, y: nat)
  requires m > 0
  ensures