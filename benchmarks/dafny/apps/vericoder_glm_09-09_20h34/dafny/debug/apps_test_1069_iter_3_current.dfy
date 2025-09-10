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
lemma StringToNatMod4(s: string)
  requires |s| >= 2
  requires ValidInput(s)
  ensures StringToNat(s) % 4 == StringToNat(s[|s|-2..]) % 4
{
  var prefix := s[..|s|-2];
  var lastTwo := s[|s|-2..];
  calc {
    StringToNat(s) % 4;
    { 
      // Break off the last character
      assert StringToNat(s) == StringToNat(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int) as nat;
    }
    (StringToNat(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)) % 4;
    { 
      // Break off the next last character
      var s1 := s[..|s|-1];
      assert StringToNat(s1) == StringToNat(s1[..|s1|-1]) * 10 + (s1[|s1|-1] as int - '0' as int) as nat;
    }
    ( (StringToNat(s[..|s|-2]) * 10 + (s[|s|-2] as int - '0' as int)) * 10 + (s[|s|-1] as int - '0' as int) ) % 4;
    ( StringToNat(s[..|s|-2]) * 100 + (s[|s|-2] as int - '0' as int)*10 + (s[|s|-1] as int - '0' as int) ) % 4;
    { 
      assert (s[|s|-2] as int - '0' as int)*10 + (s[|s|-1] as int - '0' as int) == StringToNat(lastTwo);
      assert 100 % 4 == 0;
    }
    ( StringToNat(s[..|s|-2]) * (100 % 4) + StringToNat(lastTwo) % 4 ) % 4;
    ( StringToNat(s[..|s|-2]) * 0 + StringToNat(lastTwo) % 4 ) % 4;
    ( 0 + StringToNat(lastTwo) % 4 ) % 4;
    StringToNat(lastTwo) % 4;
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
  if |n| >= 2 then {
    StringToNatMod4(n);
    if (StringToNat(n[|n|-2..]) % 4 == 0) {
      result := "4\n";
    } else {
      result := "0\n";
    }
  } else {
    if (StringToNat(n) % 4 == 0) {
      result := "4\n";
    } else {
      result := "0\n";
    }
  }
}
// </vc-code>

