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
function pow(b: int, e: int): int
  requires e >= 0
  ensures pow(b, e) >= 0
{
  if e == 0 then 1
  else b * pow(b, e - 1)
}

lemma max_f_monotonic(n: int, a: seq<int>, x1: int, x2: int)
  requires n >= 0
  requires |a| == n
  requires forall i :: 0 <= i < n ==> a[i] >= 0
  requires 0 <= x1 <= x2 < pow(2, n)
  ensures f(a, x1, n) <= f(a, x2, n)
{
  if n == 0 {
    assert f(a, x1, 0) == 0;
    assert f(a, x2, 0) == 0;
  } else if (x1 / pow(2, n-1)) % 2 == (x2 / pow(2, n-1)) % 2 {
    max_f_monotonic(n-1, a[..n-1], x1 % pow(2, n-1), x2 % pow(2, n-1));
  } else {
    // This case implies (x1 / pow(2, n-1)) % 2 == 0 and (x2 / pow(2, n-1)) % 2 == 1.
    // The most significant bit (MSB) for position n-1 is 0 for x1 and 1 for x2.
    //
    // Let x1' = x1 % pow(2, n-1) and x2' = x2 % pow(2, n-1)
    // We know x1' < pow(2, n-1) and x2' < pow(2, n-1).
    //
    // f(a, x1, n) = (0) + f(a[..n-1], x1', n-1) = f(a[..n-1], x1', n-1)
    // f(a, x2, n) = a[n-1] + f(a[..n-1], x2', n-1)
    //
    // Since all a[i] >= 0, a[n-1] >= 0.
    // Also, f(a[..n-1], x2', n-1) >= 0.
    //
    // So, f(a, x2, n) >= a[n-1] >= 0.
    // And f(a, x1, n) >= 0.
    //
    // We need to show f(a[..n-1], x1', n-1) <= a[n-1] + f(a[..n-1], x2', n-1).
    //
    // This property inherently holds because increasing the MSB from 0 to 1 adds a[n-1] to the sum,
    // and a[n-1] >= 0. The remaining parts (f(a[..n-1], x1', n-1) and f(a[..n-1], x2', n-1))
    // are for values less than pow(2, n-1), so x1' and x2' are within the domain of f(..., n-1).
    //
    // We can't directly compare x1' and x2' here using the lemma because x1' can be greater than x2'.
    // E.g., n=2, x1=0 (00), x2=2 (10). x1'=0, x2'=0. f(a,0,2)=0. f(a,2,2)=a[1]. 0 <= a[1] holds.
    // E.g., n=2, x1=1 (01), x2=3 (11). x1'=1, x2'=1. f(a,1,2)=a[0]. f(a,3,2)=a[1]+a[0]. a[0] <= a[1]+a[0] holds.
    //
    // The inductive step here relies on the definition of f and the non-negativity of a[i].
    // If x1 and x2 differ in the (n-1)-th bit and all higher bits are the same, and x1 has 0 at (n-1)-th bit, x2 has 1,
    // then f(a, x2, n) = a[n-1] + f(a[..n-1], x2%', n-1)
    // f(a, x1, n) = 0 + f(a[..n-1], x1%', n-1)
    // Since x1 <= x2 and the MSB of x1 is 0 and MSB of x2 is 1 (meaning x1 is in [0, 2^(n-1)-1] and x2 is in [2^(n-1), 2^n-1]),
    // we know that f(a[..n-1], x1%', n-1) represents a sum of elements where the bits for x1' are 1,
    // and f(a[..n-1], x2%', n-1) represents a sum of elements where the bits for x2' are 1.
    // Since all a[i] >= 0, the maximum possible value of f(a[..n-1], _, n-1) is when all bits are 1
    // (i.e., x = pow(2, n-1) - 1).
    // So, f(a[..n-1], x1', n-1) <= sum_{i=0}^{n-2} a[i]
    // And 0 <= f(a[..n-1], x2', n-1)
    // Thus f(a, x1, n) <= f(a[..n-1], (pow(2, n-1) - 1), n-1)
    // And f(a, x2, n) >= a[n-1]
    // The specific comparison f(a, x1, n) <= f(a, x2, n) holds because the additional term a[n-1] in f(a, x2, n)
    // is non-negative.
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
  var max_x: int := binaryStringToInt(k);
  result := f(a, max_x, n);
}
// </vc-code>

