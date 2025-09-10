function StringToNat(s: string): nat
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
  if |s| == 1 then (s[0] as int - '0' as int) as nat
  else StringToNat(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int) as nat
}

predicate ValidInput(n: string)
{
  |n| > 0 && 
  (forall i :: 0 <= i < |n| ==> '0' <= n[i] <= '9') &&
  (n[0] != '0' || |n| == 1)
}

predicate ValidOutput(result: string)
{
  result == "4\n" || result == "0\n"
}

// <vc-helpers>
function Pow10(k: nat): nat
  decreases k
{
  if k == 0 then 1 else Pow10(k-1) * 10
}

lemma Pow10_mul10_mod4(k: nat)
  ensures k >= 2 ==> Pow10(k) % 4 == 0
  decreases k
{
  if k == 2 {
    assert Pow10(2) == 100;
    assert Pow10(2) % 4 == 0;
  } else if k > 2 {
    Pow10_mul10_mod4(k-1);
    // Pow10(k) = Pow10(k-1) * 10, and if Pow10(k-1) divisible by 4 then so is Pow10(k)
    assert Pow10(k) == Pow10(k-1) * 10;
    assert Pow10(k-1) % 4 == 0;
    // Hence Pow10(k) % 4 == 0
    assert Pow10(k) % 4 == 0;
  }
  // k < 2 has no postcondition requirement
}

lemma Decompose_LastTwo_ge3(s: string)
  requires |s| >= 3
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToNat(s) == StringToNat(s[..|s|-2]) * 100 + ((s[|s|-2] as int - '0' as int) as nat * 10 + (s[|s|-1] as int - '0' as int) as nat)
  decreases |s|
{
  var u := s[..|s|-1];
  // StringToNat(s) = StringToNat(u) * 10 + lastDigit
  assert StringToNat(s) == StringToNat(u) * 10 + ((s[|s|-1] as int - '0' as int) as nat);
  // u has length >= 2 so we can express StringToNat(u) = StringToNat(s[..|s|-2]) * 10 + secondLastDigit
  assert StringToNat(u) == StringToNat(s[..|s|-2]) * 10 + ((s[|s|-2] as int - '0' as int) as nat);
  // combine
  assert StringToNat(s) == (StringToNat(s[..|s|-2]) * 10 + ((s[|s|-2] as int - '0' as int) as nat)) * 10 + ((s[|s|-1] as int - '0' as int) as nat);
  assert StringToNat(s) == StringToNat(s[..|s|-2]) * 100 + ((s[|s|-2] as int - '0' as int) as nat * 10 + (s[|s|-1] as int - '0' as int) as nat);
}

lemma LastTwoDigitsMod4(s: string)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures if |s| == 1 then StringToNat(s) % 4 == (((s[0] as int - '0' as int) as nat) % 4) else StringToNat(s) % 4 == (((s[|s|-2] as int - '0' as int) as nat * 10 + (s[|s|-1] as int - '0' as int) as nat) % 4)
  decreases |s|
{
  if |s| == 1 {
    // direct from definition
    assert StringToNat(s) == ((s[0] as int - '0' as int) as nat);
  } else if |s| == 2 {
    // direct from definition for length 2
    assert StringToNat(s) == ((s[0] as int - '0' as int) as nat) * 10 + ((s[1] as int - '0' as int) as nat);
  } else {
    // |s| >= 3
    Decompose_LastTwo_ge3(s);
    var prefix := StringToNat(s[..|s|-2]);
    var lastTwo := ((s[|s|-2] as int - '0' as int) as nat) * 10 + ((s[|s|-1] as int - '0' as int) as nat);
    // StringToNat(s) = prefix * 100 + lastTwo
    assert StringToNat(s) == prefix * 100 + lastTwo;
    // 100 is divisible by 4: 100 == 4 * 25
    assert prefix * 100 == 4 * (prefix * 25);
    // therefore prefix * 100 is divisible by 4, so its remainder mod 4 is 0
    assert (prefix * 100) % 4 == 0;
    // so StringToNat(s) % 4 == lastTwo % 4
    assert StringToNat(s) % 4 == lastTwo % 4;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: string) returns (result: string)
  requires ValidInput(n)
  ensures ValidOutput(result)
  ensures (StringToNat(n) % 4 == 0) <==> (result == "4\n")
  ensures (StringToNat(n) % 4 != 0) <==> (result == "0\n")
// </vc-spec>
// <vc-code>
{
  var last: nat;
  if |n| == 1 {
    last := ((n[0] as int - '0' as int) as nat);
  } else {
    last := ((n[|n|-2] as int - '0' as int) as nat) * 10 + ((n[|n|-1] as int - '0' as int) as nat);
  }

  // Relate last to StringToNat(n)
  LastTwoDigitsMod4(n);

  if last % 4 == 0 {
    result := "4\n";
  } else {
    result := "0\n";
  }

  // Use the lemma result to satisfy the ensures about StringToNat(n)
  if |n| == 1 {
    assert StringToNat(n) % 4 == last % 4;
  } else {
    assert StringToNat(n) % 4 == last % 4;
  }
}
// </vc-code>

