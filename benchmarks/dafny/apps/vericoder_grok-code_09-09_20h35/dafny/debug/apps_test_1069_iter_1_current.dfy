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
function DigitToNat(c: char): nat
  requires '0' <= c <= '9'
{
  ((c as int) - ('0' as int)) as nat
}

lemma LastTwoDecideMod4(s: string)
  requires ValidInput(s)
  requires |s| >= 2
  ensures StringToNat(s) % 4 == ((10 * DigitToNat(s[|s|-2]) + DigitToNat(s[|s|-1])) % 4)

lemma SingleDigitMod4(s: string)
  requires ValidInput(s)
  requires |s| == 1
  ensures StringToNat(s) % 4 == (DigitToNat(s[0]) % 4)

{
  var len := |n| as int;
  if len == 1 {
    var d := DigitToNat(n[0]);
    if d % 4 == 0 {
      result := "4\n";
    } else {
      result := "0\n";
    }
    SingleDigitMod4(n);
  } else {
    var x := DigitToNat(n[len - 2]);
    var y := DigitToNat(n[len - 1]);
    var last_two := 10 * x + y;
    if last_two % 4 == 0 {
      result := "4\n";
    } else {
      result := "0\n";
    }
    LastTwoDecideMod4(n);
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
function DigitToNat(c: char): nat
  requires '0' <= c <= '9'
{
  ((c as int) - ('0' as int)) as nat
}

lemma LastTwoDecideMod4(s: string)
  requires ValidInput(s)
  requires |s| >= 2
  ensures StringToNat(s) % 4 == ((10 * DigitToNat(s[|s|-2]) + DigitToNat(s[|s|-1])) % 4)

lemma SingleDigitMod4(s: string)
  requires ValidInput(s)
  requires |s| == 1
  ensures StringToNat(s) % 4 == (DigitToNat(s[0]) % 4)

{
  var len := |n| as int;
  if len == 1 {
    var d := DigitToNat(n[0]);
    if d % 4 == 0 {
      result := "4\n";
    } else {
      result := "0\n";
    }
    SingleDigitMod4(n);
  } else {
    var x := DigitToNat(n[len - 2]);
    var y := DigitToNat(n[len - 1]);
    var last_two := 10 * x + y;
    if last_two % 4 == 0 {
      result := "4\n";
    } else {
      result := "0\n";
    }
    LastTwoDecideMod4(n);
  }
}
// </vc-code>

