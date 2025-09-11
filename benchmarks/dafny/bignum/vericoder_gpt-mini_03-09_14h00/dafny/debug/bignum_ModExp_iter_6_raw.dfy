```vc-helpers
lemma MulMod(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x * y) % m == ((x % m) * (y % m)) % m
{
  var xm := x % m;
  var xq := x / m;
  var ym := y % m;
  var yq := y / m;
  assert x == xm + m * xq;
  assert y == ym + m * yq;
  assert x * y == (xm + m * xq) * (ym + m * yq);
  assert x * y == xm * ym + m * (xm * yq + xq * ym + m * xq * yq);
  assert (x * y) % m == (xm * ym) % m;
  assert ((x % m) * (y % m)) % m == (xm * ym) % m;
}

method Nat2Str(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "";
  } else {
    var prefix := Nat2Str(n / 2);
    var bit := if n % 2 == 1 then "1" else "0";
    s := prefix + bit;
    // proofs
    assert ValidBitString(prefix);
    assert Str2Int(prefix) == n / 2;
    assert |s|