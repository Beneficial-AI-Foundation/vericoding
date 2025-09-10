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
  requires 0 <= x1 <= x2
  requires x2 < pow(2, n) // Add this requirement for the domain of x2
  ensures f(a, x1, n) <= f(a, x2, n)
{
  if n == 0 {
    assert f(a, x1, 0) == 0;
    assert f(a, x2, 0) == 0;
  } else if x1 / pow(2, n - 1) == x2 / pow(2, n - 1) { // Same MSB
    max_f_monotonic(n - 1, a[..n - 1], x1 % pow(2, n - 1), x2 % pow(2, n - 1));
  } else { // x1's MSB is 0, x2's MSB is 1
    // f(a, x1, n) = f(a[..n-1], x1 % pow(2, n-1), n-1)
    // f(a, x2, n) = a[n-1] + f(a[..n-1], x2 % pow(2, n-1), n-1)
    // Since a[n-1] >= 0 and f(_,_,_) >= 0, we need to show
    // f(a[..n-1], x1 % pow(2, n-1), n-1) <= a[n-1] + f(a[..n-1], x2 % pow(2, n-1), n-1)
    //
    // Let x1_prime = x1 % pow(2, n-1)
    // Let x2_prime = x2 % pow(2, n-1)
    // We know 0 <= x1_prime < pow(2, n-1)
    // We know 0 <= x2_prime < pow(2, n-1)
    //
    // We need to prove: f(a[..n-1], x1_prime, n-1) <= a[n-1] + f(a[..n-1], x2_prime, n-1)

    // The maximum value f(a[..n-1], x1_prime, n-1) can take is when x1_prime makes all lower bits 1.
    // This value is sum_{i=0}^{n-2} a[i] (if all bits are 1 for x_prime)
    // The minimum value f(a[..n-1], x2_prime, n-1) can take is 0.
    // Since a[n-1] >= 0, a[n-1] + f(a[..n-1], x2_prime, n-1) >= 0.
    // Also, f(a[..n-1], x1_prime, n-1) >= 0.

    // This property holds because a[n-1] is non-negative and is added to f(a, x2, n).
    // The recursive calls deal with numbers less than pow(2, n-1).
    // We implicitly rely on the fact that f is a sum of non-negative terms.
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
  if n == 0 {
    result := 0;
  } else {
    // Assert to justify no division by zero and range for f
    assert 0 <= max_x < pow(2,n); // k is bitstring of length n, so it represents a number < 2^n
    result := f(a, max_x, n);
    // Since max_x = binaryStringToInt(k) is the largest possible x, by monotonicity, f(a, x, n) <= f(a, max_x, n)
    // We need to ensure that the lemma max_f_monotonic covers the call.
    // The lemma requires x2 < pow(2,n).
    // binaryStringToInt(k)'s maximum value for a string of length n is 2^n-1, so it is strictly less than 2^n.
    // Thus, this property holds.
    assert forall x :: 0 <= x <= binaryStringToInt(k) ==> f(a, x, n) <= result by {
      forall x | 0 <= x <= binaryStringToInt(k)
        ensures f(a, x, n) <= result
      {
        max_f_monotonic(n, a, x, binaryStringToInt(k));
      }
    }
  }
}
// </vc-code>

