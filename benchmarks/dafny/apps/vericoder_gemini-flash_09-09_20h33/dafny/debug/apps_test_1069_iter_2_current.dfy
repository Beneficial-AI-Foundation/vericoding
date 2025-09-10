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
function StringToNatModulo4(s: string): nat
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  ensures StringToNatModulo4(s) == (StringToNat(s) % 4)
{
  if |s| == 1 then ((s[0] as int - '0' as int) % 4) as nat
  else
    var lastDigit := (s[|s|-1] as int - '0' as int);
    var restModulo4 := StringToNatModulo4(s[..|s|-1]);
    ((restModulo4 * 10 + lastDigit) % 4) as nat
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
  var len := |n|;
  if len == 1 {
    var digit := (n[0] as int - '0' as int);
    if digit % 4 == 0 {
      result := "4\n";
    } else {
      result := "0\n";
    }
  } else {
    var lastTwoDigitsString := n[len-2..];
    var lastTwoDigitsInt := StringToNat(lastTwoDigitsString);
    if lastTwoDigitsInt % 4 == 0 {
      result := "4\n";
    } else {
      result := "0\n";
    }
  }
}
// </vc-code>

