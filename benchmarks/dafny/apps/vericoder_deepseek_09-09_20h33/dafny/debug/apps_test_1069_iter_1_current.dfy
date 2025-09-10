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
lemma ModLemma(a: string, b: int)
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> '0' <= a[i] <= '9'
  ensures StringToNat(a) % 4 == (StringToNat(a[..|a|-1]) * 10 + (a[|a|-1] as int - '0' as int)) % 4
{
}

lemma DigitModLemma(d: char)
  requires '0' <= d <= '9'
  ensures (d as int - '0' as int) % 4 >= 0
{
}

lemma StringModHelper(a: string, b: string)
  requires |a| > 0 && |b| > 0
  requires forall i :: 0 <= i < |a| ==> '0' <= a[i] <= '9'
  requires forall i :: 0 <= i < |b| ==> '0' <= b[i] <= '9'
  requires a[..|a|-1] == b
  ensures StringToNat(a) % 4 == (StringToNat(b) * 10 + (a[|a|-1] as int - '0' as int)) % 4
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
  var lastTwoDigits := if |n| >= 2 then n[|n|-2..] else n;
  var num := StringToNat(lastTwoDigits) % 4;
  
  if num == 0 {
    result := "4\n";
  } else {
    result := "0\n";
  }
}
// </vc-code>

