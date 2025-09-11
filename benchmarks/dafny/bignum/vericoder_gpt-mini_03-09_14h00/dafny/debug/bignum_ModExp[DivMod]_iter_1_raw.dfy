```vc-helpers
// Helper: convert a natural number n (< 2^len) to a bitstring of length len
method NatToBits(n: nat, len: nat) returns (s: string)
  requires n < Exp_int(2, len)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  ensures |s| == len
  decreases len
{
  if len == 0 {
    // only possible n is 0
    assert n == 0;
    s := "";
  } else {
    var n_div := n / 2;
    var n_mod := n % 2;
    var tail := NatToBits(n_div, len - 1);
    var last := if n_mod == 1 then "1" else "0";
    s := tail + last;
    // tail has length len-1
    assert |tail| == len - 1;
    // By definition of Str2Int, for s of length len:
    // Str2Int(s) == 2 * Str2Int(s[0..len-1]) + bit_last
    // Here s[0..len-1] == tail, and bit_last == n_mod
    assert Str2Int(tail) == n_div;
    if n_mod == 1 {
      assert last[0] == '1';
    } else {
      assert last[0] == '0';
    }
    // compute Str2Int(s) using definition
    assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
    // s[0..|s|-1] is tail
    assert s[0..|s|-1] == tail;
    // therefore
    assert Str2Int(s) == 2 * Str2Int(tail) + n_mod;
    // and since Str2Int(tail) == n_div and n = 2*n_div + n_mod
    assert n == 2 * n_div + n_mod;
    assert Str2Int(s) == n;
  }
  // ValidBitString holds because tail is valid and last is '0' or '1'
  if len > 0 {
    assert forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1';
  } else {
    assert forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1';
  }
}

// Lemma: for any string s, Str2Int(s) < 2^{|s|}
lemma Str2Int_lt_pow(s: string)
  ensures Str2Int(s) < Exp_int(2, |s|)
  decreases |s|
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
    assert Exp_int(2, 0) == 1;
    assert 0 < 1;
  } else {
    var pref := s[0..|s|-1];
    Str2Int_lt_pow(pref);
    var bit := if s[|s|-1] == '1' then 1 else 0;
    assert Str2Int(s) == 2 * Str2Int(pref) + bit;
    // by IH Str2Int(pref) < 2^{|pref|}
    assert Str2Int(pref) < Exp_int(2, |pref|);
    // therefore 2*Str2Int(pref) + bit <= 2*(2^{|pref|}-1) + 1 = 2^{|s|} - 1 < 2^{|s|}
    assert 2 * Str2Int(pref) + bit