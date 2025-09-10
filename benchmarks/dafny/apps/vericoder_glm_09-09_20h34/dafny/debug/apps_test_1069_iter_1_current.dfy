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
  requires ValidInput(s)
  ensures StringToNat(s) % 4 == (if |s| >= 2 then (StringToNat(s[|s|-2..]) % 4) else (StringToNat(s) % 4))
{
  if |s| == 1 {
    // Base case: single digit, no change needed
  } else {
    // Recursive case for longer strings
    calc {
      StringToNat(s) % 4;
      { 
        assert s == s[..|s|-2] + s[|s|-2..];
        assert StringToNat(s[..|s|-2] + s[|s|-2..]) == StringToNat(s[..|s|-2]) * 10 + StringToNat(s[|s|-2..]);
      }
      (StringToNat(s[..|s|-2]) * 10 + StringToNat(s[|s|-2..])) % 4;
      (StringToNat(s[..|s|-2]) * (10 % 4) + StringToNat(s[|s|-2..])) % 4;
      (StringToNat(s[..|s|-2]) * 2 + StringToNat(s[|s|-2..])) % 4;
    }
    
    // Apply induction hypothesis to the prefix
    StringToNatMod4(s[|s|-2..]);
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

