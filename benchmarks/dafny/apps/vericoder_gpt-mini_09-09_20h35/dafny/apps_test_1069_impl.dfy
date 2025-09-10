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
    assert Pow10(k) == Pow10(k-1) * 10;
    assert Pow10(k-1) % 4 == 0;
    assert Pow10(k) % 4 == 0;
  }
}

lemma LastTwoDigitsMod4(s: string)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures if |s| == 1 then StringToNat(s) % 4 == (((s[0] as int - '0' as int) as nat) % 4) else StringToNat(s) % 4 == (((s[|s|-2] as int - '0' as int) as nat * 10 + (s[|s|-1] as int - '0' as int) as nat) % 4)
  decreases |s|
{
  if |s| == 1 {
    assert StringToNat(s) == ((s[0] as int - '0' as int) as nat);
  } else if |s| == 2 {
    assert StringToNat(s) == ((s[0] as int - '0' as int) as nat) * 10 + ((s[1] as int - '0' as int) as nat);
  } else {
    var prefix := s[..|s|-2];
    var d1 := ((s[|s|-2] as int - '0' as int) as nat);
    var d2 := ((s[|s|-1] as int - '0' as int) as nat);
    // Let t be s without its last character
    var t := s[..|s|-1];
    // Unfold StringToNat(s) once
    assert StringToNat(s) == StringToNat(t) * 10 + d2;
    // Unfold StringToNat(t) once (t has length >= 2)
    assert StringToNat(t) == StringToNat(t[..|t|-1]) * 10 + ((t[|t|-1] as int - '0' as int) as nat);
    // Relate slices: t[..|t|-1] == prefix and t[|t|-1] == s[|s|-2]
    assert t[..|t|-1] == prefix;
    assert ((t[|t|-1] as int - '0' as int) as nat) == d1;
    // Substitute to get decomposition in terms of prefix, d1, d2
    assert StringToNat(t) == StringToNat(prefix) * 10 + d1;
    assert StringToNat(s) == (StringToNat(prefix) * 10 + d1) * 10 + d2;
    assert StringToNat(s) == StringToNat(prefix) * 100 + (d1 * 10 + d2);
    var prefixNat := StringToNat(prefix);
    // prefixNat * 100 is divisible by 4 since prefixNat * 100 = 4 * (prefixNat * 25)
    assert prefixNat * 100 == 4 * (prefixNat * 25);
    assert (prefixNat * 100) % 4 == 0;
    // hence remainder of StringToNat(s) modulo 4 equals that of last two digits
    assert StringToNat(s) % 4 == (d1 * 10 + d2) % 4;
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
  assert StringToNat(n) % 4 == last % 4;
}
// </vc-code>

