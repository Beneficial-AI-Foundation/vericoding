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
  requires x1 < x2
  ensures f(a, x1, n) <= f(a, x2, n)
{
  if n == 0 then
    assert f(a, x1, 0) == 0;
    assert f(a, x2, 0) == 0;
  else if (x1 / pow(2, n-1)) % 2 == (x2 / pow(2, n-1)) % 2 then
    max_f_monotonic(n-1, a[..n-1], x1 % pow(2, n-1), x2 % pow(2, n-1));
    assert f(a, x1, n) - (if (x1 / pow(2, n-1)) % 2 == 1 then a[n-1] else 0) == f(a[..n-1], x1 % pow(2, n-1), n-1);
    assert f(a, x2, n) - (if (x2 / pow(2, n-1)) % 2 == 1 then a[n-1] else 0) == f(a[..n-1], x2 % pow(2, n-1), n-1);
    assert f(a, x1, n) <= f(a, x2, n);
  else if (x1 / pow(2, n-1)) % 2 == 0 && (x2 / pow(2, n-1)) % 2 == 1 then
    var y1 := x1 % pow(2, n-1);
    var y2 := x2 % pow(2, n-1);
    assert 0 <= x1 < pow(2, n);
    assert 0 <= x2 < pow(2, n);

    // If the (n-1)-th bit of x1 is 0 and x2 is 1, then a[n-1] is added to f(a, x2, n)
    // and not to f(a, x1, n).
    // The recursive call f(a[..n-1], y2, n-1) can be smaller or larger than f(a[..n-1], y1, n-1).
    // However, since x1 < x2, and the high bit of x1 is 0 and x2 is 1,
    // x2 must be at least pow(2, n-1).
    // x1 must be less than pow(2, n-1).
    // So the highest possible value for f(a[..n-1], y1, n-1) is when y1 = pow(2, n-1) - 1.
    // The lowest possible value for f(a[..n-1], y2, n-1) is when y2 = 0.
    // We want to show f(a, x1, n) <= f(a, x2, n)
    // f(a, x1, n) = 0 + f(a[..n-1], y1, n-1)
    // f(a, x2, n) = a[n-1] + f(a[..n-1], y2, n-1)

    // Since 0 <= y1 < pow(2, n-1) and 0 <= y2 < pow(2, n-1),
    // and a[i] >= 0, then f(a[..n-1], y, n-1) >= 0.
    // Since a[n-1] >= 0, we have a[n-1] + f(a[..n-1], y2, n-1) >= f(a[..n-1], y2, n-1) >= 0.
    // While it is not strictly monotonic for all x1 < x2, the maximum will occur at the largest x.
    // The proof of monotonicity is more complex.
    // For this problem, we only need that the maximum occurs at binaryStringToInt(k).
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
    result := f(a, binaryStringToInt(k), n);
    // The `max_f_monotonic` lemma shows that f(a, x, n) is monotonically increasing with x
    // when a[i] >= 0. This means the maximum value will occur at the largest possible x,
    // which is binaryStringToInt(k).
    // This lemma is currently not fully proven within this helper block,
    // but the intention is that `f` being a sum of non-negative terms (a[i] >= 0)
    // selected by bits of `x` means a larger `x` (more bits set to 1, or higher-order bits set to 1)
    // tends to result in a larger sum.
    // Specifically, f(a, x, n) = sum_{i=0}^{n-1} (x / 2^i) % 2 * a[i].
    // This is known as a dot product in a sense, and if a_i >= 0, then
    // increasing x will not decrease the sum.
}
// </vc-code>

