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
lemma fNonNegative(a: seq<int>, x: int, n: int)
  requires n >= 0
  requires |a| == n
  requires forall i :: 0 <= i < n ==> a[i] >= 0
  requires x >= 0
  ensures f(a, x, n) >= 0
{
  if n == 0 {
    assert f(a, x, n) == 0;
  } else {
    pow2Positive(n-1);
    assert pow(2, n-1) > 0;
    assert f(a, x, n) == (if (x / pow(2, n-1)) % 2 == 1 then a[n-1] else 0) + f(a[..n-1], x % pow(2, n-1), n-1);
    assert x % pow(2, n-1) >= 0;
    fNonNegative(a[..n-1], x % pow(2, n-1), n-1);
  }
}

lemma pow2Positive(n: int)
  requires n >= 0
  ensures pow(2, n) > 0
{
  if n == 0 {
    assert pow(2, 0) == 1;
  } else {
    assert pow(2, n) == 2 * pow(2, n-1);
    pow2Positive(n-1);
  }
}

lemma binaryStringToIntNonNegative(s: string)
  requires isBinaryString(s)
  ensures binaryStringToInt(s) >= 0
{
  if |s| == 0 {
    assert binaryStringToInt(s) == 0;
  } else {
    assert isBinaryString(s[1..]);
    binaryStringToIntNonNegative(s[1..]);
    pow2Positive(|s|-1);
    assert pow(2, |s|-1) > 0;
    assert binaryStringToInt(s[1..]) >= 0;
    assert (if s[0] == '1' then 1 else 0) >= 0;
    assert binaryStringToInt(s) == (if s[0] == '1' then 1 else 0) * pow(2, |s|-1) + binaryStringToInt(s[1..]);
  }
}

lemma binaryStringToIntBound(s: string)
  requires isBinaryString(s)
  ensures binaryStringToInt(s) < pow(2, |s|)
{
  if |s| == 0 {
    assert binaryStringToInt(s) == 0;
    assert pow(2, 0) == 1;
  } else {
    assert binaryStringToInt(s) == (if s[0] == '1' then 1 else 0) * pow(2, |s|-1) + binaryStringToInt(s[1..]);
    binaryStringToIntBound(s[1..]);
    pow2Positive(|s|-1);
    assert binaryStringToInt(s[1..]) < pow(2, |s[1..]|);
    assert |s[1..]| == |s| - 1;
    assert pow(2, |s|) == 2 * pow(2, |s|-1);
  }
}

function pow(base: int, exp: int): int
  requires exp >= 0
  ensures exp == 0 ==> pow(base, exp) == 1
  ensures exp > 0 ==> pow(base, exp) == base * pow(base, exp - 1)
  ensures base > 0 ==> pow(base, exp) > 0
{
  if exp == 0 then 1
  else base * pow(base, exp - 1)
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
  binaryStringToIntNonNegative(k);
  var bestX := 0;
  var maxSum := f(a, 0, n);
  
  fNonNegative(a, 0, n);
  
  var x := 1;
  var limit := binaryStringToInt(k);
  
  while x <= limit
    invariant 0 <= bestX <= limit
    invariant maxSum == f(a, bestX, n)
    invariant maxSum >= 0
    invariant forall y :: 0 <= y < x ==> f(a, y, n) <= maxSum
    decreases limit - x + 1
  {
    fNonNegative(a, x, n);
    var currentSum := f(a, x, n);
    if currentSum > maxSum {
      maxSum := currentSum;
      bestX := x;
    }
    x := x + 1;
  }
  
  result := maxSum;
}
// </vc-code>

