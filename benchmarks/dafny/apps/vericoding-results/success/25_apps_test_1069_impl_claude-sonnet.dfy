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
lemma LastTwoDigitsModulo(s: string)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToNat(s) % 4 == (if |s| == 1 then StringToNat(s) % 4 
                                 else if |s| == 2 then StringToNat(s) % 4
                                 else StringToNat(s[|s|-2..]) % 4)
{
  if |s| <= 2 {
    // Base cases
  } else {
    var prefix := s[..|s|-2];
    var lastTwo := s[|s|-2..];
    
    calc {
      StringToNat(s) % 4;
    ==
      (StringToNat(prefix) * 100 + StringToNat(lastTwo)) % 4;
    ==  { assert 100 % 4 == 0; }
      ((StringToNat(prefix) * 100) % 4 + StringToNat(lastTwo) % 4) % 4;
    ==  { assert (StringToNat(prefix) * 100) % 4 == 0; }
      (0 + StringToNat(lastTwo) % 4) % 4;
    ==
      StringToNat(lastTwo) % 4;
    }
  }
}

lemma SingleDigitMod4(c: char)
  requires '0' <= c <= '9'
  ensures (c as int - '0' as int) % 4 == 
    if c == '0' || c == '4' || c == '8' then 0
    else if c == '1' || c == '5' || c == '9' then 1
    else if c == '2' || c == '6' then 2
    else 3
{
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
  LastTwoDigitsModulo(n);
  
  if |n| == 1 {
    SingleDigitMod4(n[0]);
    if n[0] == '0' || n[0] == '4' || n[0] == '8' {
      result := "4\n";
    } else {
      result := "0\n";
    }
  } else {
    var lastTwo := n[|n|-2..];
    var num := StringToNat(lastTwo);
    
    if num % 4 == 0 {
      result := "4\n";
    } else {
      result := "0\n";
    }
  }
}
// </vc-code>

