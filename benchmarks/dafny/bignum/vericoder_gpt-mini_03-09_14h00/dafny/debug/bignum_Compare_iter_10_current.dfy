ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
ghost function pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

lemma Str2Int_sum(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == (sum i | 0 <= i < |s| :: if s[i] == '1' then pow2(|s| - 1 - i) else 0)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var prefix := s[0..|s|-1];
    var last := s[|s|-1];
    Str2Int_sum(prefix);
    calc {
      Str2Int(s);
      == { }
      2 * Str2Int(prefix) + (if last == '1' then 1 else 0);
      == { assert Str2Int(prefix) == (sum i | 0 <= i < |prefix| :: if prefix[i] == '1' then pow2(|prefix| - 1 - i) else 0); }
      2 * (sum i | 0 <= i < |prefix| :: if prefix[i] == '1' then pow2(|prefix| - 1 - i) else 0) + (if last == '1' then 1 else 0);
      == { }
      (sum i | 0 <= i < |prefix| :: if prefix[i] == '1' then 2 * pow2(|prefix| - 1 - i) else 0) + (if last == '1' then 1 else 0);
      == { }
      (sum i | 0 <= i < |prefix| :: if prefix[i] == '1' then pow2(|s| - 1 - i) else 0) + (if last == '1' then pow2(0) else 0);
      == { }
      (sum i | 0 <= i < |s| :: if s[i] == '1' then pow2(|s| - 1 - i) else 0);
    }
  }
}

lemma SumPow_identity(n: nat)
  ensures (sum k | 0 <= k < n :: pow2(k)) == pow2(n) - 1
  decreases n
{
  if n == 0 {
    assert (sum k | 0 <= k < 0 :: pow2(k)) == 0;
    assert pow2(0) - 1 == 0;
  } else {
    SumPow_identity(n - 1);
    calc {
      (sum k | 0 <= k < n :: pow2(k));
      == { }
      (sum k | 0 <= k < n - 1 :: pow2(k)) + pow2(n - 1);
      == { assert (sum k | 0 <= k < n - 1 :: pow2(k)) == pow2(n - 1) - 1; }
      (pow2(n - 1) - 1) + pow2(n - 1);
      == { }
      2 * pow2(n - 1) - 1;
      == { assert pow2(n) == 2 * pow2(n - 1); }
      pow2(n) - 1;
    }
  }
}

lemma Str2Int_upper_bound(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) <= pow2(|s|) - 1
  decreases |s|
{
  Str2Int_sum(s);
  if |s| == 0 {
    assert Str2Int(s) == 0;
    assert pow2(0) - 1 == 0;
  } else {
    // Each bit contribution <= corresponding pow2, so sum <= sum pow2
    assert (sum i | 0 <= i < |s| :: if s[i] == '1' then pow2(|s| - 1 - i) else 0) <= (sum i | 0 <= i < |s| :: pow2(|s| - 1 - i));
    assert (sum i | 0 <= i < |s| :: pow2(|s
// </vc-helpers>

// <vc-spec>
method Compare(s1: string, s2: string) returns (res: int)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1
  ensures Str2Int(s1) == Str2Int(s2) ==> res == 0
  ensures Str2Int(s1) > Str2Int(s2) ==> res == 1
  decreases Str2Int(s1) + Str2Int(s2)
// </vc-spec>
// <vc-code>
ghost function pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

lemma Str2Int_sum(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == (sum i | 0 <= i < |s| :: if s[i] == '1' then pow2(|s| - 1 - i) else 0)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var prefix := s[0..|s|-1];
    var last := s[|s|-1];
    Str2Int_sum(prefix);
    calc {
      Str2Int(s);
      == { }
      2 * Str2Int(prefix) + (if last == '1' then 1 else 0);
      == { assert Str2Int(prefix) == (sum i | 0 <= i < |prefix| :: if prefix[i] == '1' then pow2(|prefix| - 1 - i) else 0); }
      2 * (sum i | 0 <= i < |prefix| :: if prefix[i] == '1' then pow2(|prefix| - 1 - i) else 0) + (if last == '1' then 1 else 0);
      == { }
      (sum i | 0 <= i < |prefix| :: if prefix[i] == '1' then 2 * pow2(|prefix| - 1 - i) else 0) + (if last == '1' then 1 else 0);
      == { }
      (sum i | 0 <= i < |prefix| :: if prefix[i] == '1' then pow2(|s| - 1 - i) else 0) + (if last == '1' then pow2(0) else 0);
      == { }
      (sum i | 0 <= i < |s| :: if s[i] == '1' then pow2(|s| - 1 - i) else 0);
    }
  }
}

lemma SumPow_identity(n: nat)
  ensures (sum k | 0 <= k < n :: pow2(k)) == pow2(n) - 1
  decreases n
{
  if n == 0 {
    assert (sum k | 0 <= k < 0 :: pow2(k)) == 0;
    assert pow2(0) - 1 == 0;
  } else {
    SumPow_identity(n - 1);
    calc {
      (sum k | 0 <= k < n :: pow2(k));
      == { }
      (sum k | 0 <= k < n - 1 :: pow2(k)) + pow2(n - 1);
      == { assert (sum k | 0 <= k < n - 1 :: pow2(k)) == pow2(n - 1) - 1; }
      (pow2(n - 1) - 1) + pow2(n - 1);
      == { }
      2 * pow2(n - 1) - 1;
      == { assert pow2(n) == 2 * pow2(n - 1); }
      pow2(n) - 1;
    }
  }
}

lemma Str2Int_upper_bound(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) <= pow2(|s|) - 1
  decreases |s|
{
  Str2Int_sum(s);
  if |s| == 0 {
    assert Str2Int(s) == 0;
    assert pow2(0) - 1 == 0;
  } else {
    // Each bit contribution <= corresponding pow2, so sum <= sum pow2
    assert (sum i | 0 <= i < |s| :: if s[i] == '1' then pow2(|s| - 1 - i) else 0) <= (sum i | 0 <= i < |s| :: pow2(|s| - 1 - i));
    assert (sum i | 0 <= i < |s| :: pow2(|s
// </vc-code>

