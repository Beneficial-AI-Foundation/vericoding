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
function pow(base: int, exp: int): int
  requires base >= 0 && exp >= 0
  ensures pow(base, exp) >= 1
{
  if exp == 0 then 1
  else if base == 0 then 1
  else base * pow(base, exp - 1)
}

lemma PowMonotonic(base: int, exp1: int, exp2: int)
  requires base >= 2 && exp1 >= 0 && exp2 >= exp1
  ensures pow(base, exp1) <= pow(base, exp2)
{
  if exp1 == exp2 {
  } else {
    PowMonotonic(base, exp1, exp2 - 1);
  }
}

lemma BinaryStringNonNegative(s: string)
  requires isBinaryString(s)
  ensures binaryStringToInt(s) >= 0
{
}

lemma FunctionFProperties(a: seq<int>, x: int, n: int)
  requires n >= 0 && |a| == n
  requires forall i :: 0 <= i < n ==> a[i] >= 0
  ensures f(a, x, n) >= 0
{
  if n == 0 {
  } else {
    FunctionFProperties(a[..n-1], x % pow(2, n-1), n-1);
  }
}

lemma SliceLengthProperty(a: seq<int>, k: int)
  requires 0 < k <= |a|
  ensures |a[..k-1]| == k-1
{
}

lemma GreedyOptimal(a: seq<int>, n: int, limit: int, x: int)
  requires n >= 0 && |a| == n
  requires forall i :: 0 <= i < n ==> a[i] >= 0
  requires 0 <= x <= limit
  requires forall i :: 0 <= i < n ==> (x / pow(2, i)) % 2 == (if a[i] > 0 && x + pow(2, i) <= limit then 1 else 0)
  ensures forall y :: 0 <= y <= limit ==> f(a, y, n) <= f(a, x, n)
{
  forall y | 0 <= y <= limit ensures f(a, y, n) <= f(a, x, n) {
    GreedyOptimalHelper(a, n, limit, x, y, n);
  }
}

lemma GreedyOptimalHelper(a: seq<int>, n: int, limit: int, x: int, y: int, k: int)
  requires n >= 0 && |a| == n && 0 <= k <= n
  requires forall i :: 0 <= i < n ==> a[i] >= 0
  requires 0 <= x <= limit && 0 <= y <= limit
  requires forall i :: 0 <= i < n ==> (x / pow(2, i)) % 2 == (if a[i] > 0 && x + pow(2, i) <= limit then 1 else 0)
  ensures f(a, y, k) <= f(a, x, k)
{
  if k == 0 {
  } else {
    SliceLengthProperty(a, k);
    assert |a[..k-1]| == k-1;
    assert forall i :: 0 <= i < k-1 ==> a[..k-1][i] == a[i];
    assert forall i :: 0 <= i < k-1 ==> (x / pow(2, i)) % 2 == (if a[..k-1][i] > 0 && x + pow(2, i) <= limit then 1 else 0);
    GreedyOptimalHelper(a[..k-1], k-1, limit, x % pow(2, k-1), y % pow(2, k-1), k-1);
  }
}

lemma GreedyInvariantMaintained(a: seq<int>, n: int, limit: int, x: int, i: int)
  requires n >= 0 && |a| == n
  requires forall j :: 0 <= j < n ==> a[j] >= 0
  requires 0 <= i < n
  requires 0 <= x <= limit
  requires forall j :: i < j < n ==> (x / pow(2, j)) % 2 == (if a[j] > 0 && x + pow(2, j) <= limit then 1 else 0)
  ensures forall j :: i-1 < j < n ==> ((if a[i] > 0 && x + pow(2, i) <= limit then x + pow(2, i) else x) / pow(2, j)) % 2 == (if a[j] > 0 && (if a[i] > 0 && x + pow(2, i) <= limit then x + pow(2, i) else x) + pow(2, j) <= limit then 1 else 0)
{
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
  var x := 0;
  var i := n - 1;
  var limit := binaryStringToInt(k);
  
  while i >= 0
    invariant -1 <= i < n
    invariant 0 <= x <= limit
    invariant forall j :: 0 <= j < n ==> a[j] >= 0
    invariant forall j :: i < j < n ==> (x / pow(2, j)) % 2 == (if a[j] > 0 && x + pow(2, j) <= limit then 1 else 0)
  {
    if a[i] > 0 && x + pow(2, i) <= limit {
      x := x + pow(2, i);
    }
    GreedyInvariantMaintained(a, n, limit, x, i);
    i := i - 1;
  }
  
  FunctionFProperties(a, x, n);
  GreedyOptimal(a, n, limit, x);
  result := f(a, x, n);
}
// </vc-code>

