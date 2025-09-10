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
lemma ModLemma(a: string)
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> '0' <= a[i] <= '9'
  ensures StringToNat(a) % 4 == (StringToNat(a[..|a|-1]) * 10 + (a[|a|-1] as int - '0' as int)) % 4
{
  if |a| > 1 {
    assert a[..|a|-1] == a[..|a|-1];
    StringModHelper(a, a[..|a|-1]);
  } else {
    // Base case: single digit
    assert StringToNat(a) == (a[0] as int - '0' as int) as nat;
    assert a[..|a|-1] == a[..0] == "";
  }
}

lemma StringModHelper(a: string, b: string)
  requires |a| > 0 && |b| > 0
  requires forall i :: 0 <= i < |a| ==> '0' <= a[i] <= '9'
  requires forall i :: 0 <= i < |b| ==> '0' <= b[i] <= '9'
  requires a[..|a|-1] == b
  ensures StringToNat(a) % 4 == (StringToNat(b) * 10 + (a[|a|-1] as int - '0' as int)) % 4
{
  var lastDigit := a[|a|-1] as int - '0' as int;
  assert StringToNat(a) == StringToNat(b) * 10 + lastDigit;
  calc {
    StringToNat(a) % 4;
    ==
    (StringToNat(b) * 10 + lastDigit) % 4;
    ==
    ((StringToNat(b) % 4) * (10 % 4) + lastDigit % 4) % 4;
    ==
    ((StringToNat(b) % 4) * 2 + lastDigit % 4) % 4;
  }
}

lemma LastTwoDigitsLemma(n: string, lastTwo: string)
  requires ValidInput(n)
  requires lastTwo == if |n| >= 2 then n[|n|-2..] else n
  ensures StringToNat(n) % 4 == StringToNat(lastTwo) % 4
{
  if |n| >= 2 {
    var prefix := n[..|n|-2];
    var suffix := n[|n|-2..];
    assert n == prefix + suffix;
    assert |suffix| == 2;
    
    // Prove the numeric relationship using mathematical induction
    if |prefix| > 0 {
      var temp := prefix + suffix[0..1];
      assert |temp| > 0;
      assert forall i :: 0 <= i < |temp| ==> '0' <= temp[i] <= '9';
      
      assert StringToNat(n) == StringToNat(temp) * 10 + (suffix[1] as int - '0' as int);
      assert StringToNat(temp) == StringToNat(prefix) * 10 + (suffix[0] as int - '0' as int);
      assert StringToNat(n) == (StringToNat(prefix) * 100) + ((suffix[0] as int - '0' as int) * 10 + (suffix[1] as int - '0' as int));
    } else {
      assert StringToNat(n) == StringToNat(suffix);
    }
    
    // Since 100 ≡ 0 mod 4, the result follows
    assert (100 % 4 == 0);
    assert (StringToNat(prefix) * 100) % 4 == 0;
    assert ((StringToNat(prefix) * 100) + StringToNat(suffix)) % 4 == StringToNat(suffix) % 4;
  } else {
    assert lastTwo == n;
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
  var lastTwoDigits := if |n| >= 2 then n[|n|-2..] else n;
  
  // Explicitly prove the preconditions for StringToNat on lastTwoDigits
  assert |lastTwoDigits| > 0;
  assert forall i :: 0 <= i < |lastTwoDigits| ==> '0' <= lastTwoDigits[i] <= '9';
  
  LastTwoDigitsLemma(n, lastTwoDigits);
  
  assert |lastTwoDigits| > 0;
  assert forall i :: 0 <= i < |lastTwoDigits| ==> '0' <= lastTwoDigits[i] <= '9';
  var num := StringToNat(lastTwoDigits) % 4;
  
  if num == 0 {
    result := "4\n";
  } else {
    result := "0\n";
  }
}
// </vc-code>

