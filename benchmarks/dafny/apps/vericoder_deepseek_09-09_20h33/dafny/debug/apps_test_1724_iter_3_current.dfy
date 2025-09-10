predicate ValidInput(n: int, a: seq<int>, k: string)
{
  n >= 1 && |a| == n && |k| == n && 
  (forall i :: 0 <= i < n ==> a[i] >= 0) &&
  isBinaryString(k)
}

predicate isBinaryString(s: string)
{
  forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

function binaryStringToInt(s: string): int
  requires isBinaryString(s)
  ensures binaryStringToInt(s) >= 0
{
  if |s| == 0 then 0
  else (if s[0] == '1' then 1 else 0) * pow(2, |s|-1) + binaryStringToInt(s[1..])
}

function f(a: seq<int>, x: int, n: int): int
  requires n >= 0
  requires |a| == n
  ensures (forall i :: 0 <= i < n ==> a[i] >= 0) ==> f(a, x, n) >= 0
{
  if n == 0 then 0
  else (if (x / pow(2, n-1)) % 2 == 1 then a[n-1] else 0) + f(a[..n-1], x % pow(2, n-1), n-1)
}

// <vc-helpers>
function pow(base: int, exp: nat): int
  ensures exp == 0 ==> pow(base, exp) == 1
  ensures exp > 0 ==> pow(base, exp) == base * pow(base, exp - 1)
  ensures base >= 0 ==> pow(base, exp) >= 0
{
  if exp == 0 then 1
  else base * pow(base, exp - 1)
}

lemma pow_pos(base: int, exp: nat)
  ensures base >= 0 ==> pow(base, exp) >= 0
{
}

lemma pow_non_zero(exp: nat)
  ensures exp > 0 ==> pow(2, exp) > 0
{
  if exp > 0 {
    pow_non_zero(exp - 1);
  }
}

lemma binaryStringToInt_monotonic(s1: string, s2: string)
  requires isBinaryString(s1) && isBinaryString(s2) && |s1| == |s2|
  requires forall i :: 0 <= i < |s1| ==> s1[i] >= s2[i]
  ensures binaryStringToInt(s1) >= binaryStringToInt(s2)
{
  if |s1| == 0 {
    return;
  }
  var b1 := if s1[0] == '1' then 1 else 0;
  var b2 := if s2[0] == '1' then 1 else 0;
  if b1 > b2 {
    assert binaryStringToInt(s1) >= binaryStringToInt(s2) + pow(2, |s1| - 1);
  } else if b1 == b2 {
    binaryStringToInt_monotonic(s1[1..], s2[1..]);
  }
}

function f(a: seq<int>, x: int, n: int): int
  requires n >= 0
  requires |a| == n
  requires n > 0 ==> pow(2, n-1) > 0
  ensures (forall i :: 0 <= i < n ==> a[i] >= 0) ==> f(a, x, n) >= 0
{
  if n == 0 then 0
  else 
    var power := pow(2, n-1);
    var bit := if power > 0 then (x / power) % 2 else 0;
    (if bit == 1 then a[n-1] else 0) + f(a[..n-1], if power > 0 then x % power else x, n-1)
}

lemma f_monotonic(a: seq<int>, x1: int, x2: int, n: int)
  requires n >= 0
  requires |a| == n
  requires 0 <= x1 <= x2
  requires forall i :: 0 <= i < n ==> a[i] >= 0
  requires n > 0 ==> pow(2, n-1) > 0
  ensures f(a, x1, n) <= f(a, x2, n)
{
  if n == 0 {
    return;
  }
  var power := pow(2, n-1);
  var bit1 := if power > 0 then (x1 / power) % 2 else 0;
  var bit2 := if power > 0 then (x2 / power) % 2 else 0;
  
  if bit2 == 1 {
    if bit1 == 1 {
      f_monotonic(a[..n-1], x1 % power, x2 % power, n-1);
      assert a[n-1] + f(a[..n-1], x1 % power, n-1) <= a[n-1] + f(a[..n-1], x2 % power, n-1);
    } else {
      f_monotonic(a[..n-1], x1 % power, x2 % power, n-1);
      assert f(a[..n-1], x1 % power, n-1) <= f(a[..n-1], x2 % power, n-1);
    }
  } else {
    if bit1 == 1 {
      f_monotonic(a[..n-1], x1 % power, x2, n-1);
      assert a[n-1] + f(a[..n-1], x1 % power, n-1) >= f(a[..n-1], x2, n-1);
    } else {
      f_monotonic(a[..n-1], x1 % power, x2, n-1);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, k: string) returns (result: int)
  requires ValidInput(n, a, k)
  ensures result >= 0
  ensures exists x :: 0 <= x <= binaryStringToInt(k) && result == f(a, x, n)
  ensures forall x :: 0 <= x <= binaryStringToInt(k) ==> f(a, x, n) <= result
// </vc-spec>
// <vc-code>
{
  result := 0;
  var max := binaryStringToInt(k);
  if n > 0 {
    pow_non_zero(n-1);
  }
  result := f(a, max, n);
}
// </vc-code>

