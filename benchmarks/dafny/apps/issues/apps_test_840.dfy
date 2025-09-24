// <vc-preamble>
function canMake(a: seq<int>, b: seq<int>, k: int, numCookies: int): bool
  requires |a| == |b|
  requires numCookies >= 0
{
  calculateDeficit(a, b, numCookies, 0) <= k
}

function calculateDeficit(a: seq<int>, b: seq<int>, numCookies: int, index: int): int
  requires |a| == |b|
  requires 0 <= index <= |a|
  requires numCookies >= 0
  decreases |a| - index
{
  if index == |a| then
    0
  else
    var needed := a[index] * numCookies;
    var currentDeficit := if needed > b[index] then needed - b[index] else 0;
    currentDeficit + calculateDeficit(a, b, numCookies, index + 1)
}
// </vc-preamble>

// <vc-helpers>
lemma deficitZeroLemma(a: seq<int>, b: seq<int>, numCookies: int)
  requires |a| == |b|
  requires numCookies == 0
  requires forall i :: 0 <= i < |a| ==> b[i] >= 1
  ensures calculateDeficit(a, b, numCookies, 0) == 0
{
  deficitZeroHelper(a, b, numCookies, 0);
}

lemma deficitZeroHelper(a: seq<int>, b: seq<int>, numCookies: int, index: int)
  requires |a| == |b|
  requires numCookies == 0
  requires 0 <= index <= |a|
  requires forall i :: 0 <= i < |a| ==> b[i] >= 1
  ensures calculateDeficit(a, b, numCookies, index) == 0
  decreases |a| - index
{
  if index < |a| {
    deficitZeroHelper(a, b, numCookies, index + 1);
    assert calculateDeficit(a, b, numCookies, index + 1) == 0;
    var needed := a[index] * numCookies;
    assert needed == 0;
    var currentDeficit := if needed > b[index] then needed - b[index] else 0;
    assert needed <= b[index];
    assert currentDeficit == 0;
    assert calculateDeficit(a, b, numCookies, index) == currentDeficit + calculateDeficit(a, b, numCookies, index + 1);
    assert calculateDeficit(a, b, numCookies, index) == 0;
  }
}

lemma deficitNonNegativeLemma(a: seq<int>, b: seq<int>, numCookies: int, index: int)
  requires |a| == |b|
  requires 0 <= index <= |a|
  requires numCookies >= 0
  ensures calculateDeficit(a, b, numCookies, index) >= 0
  decreases |a| - index
{
  if index < |a| {
    deficitNonNegativeLemma(a, b, numCookies, index + 1);
  }
}

lemma deficitLargeNumCookiesLemma(a: seq<int>, b: seq<int>, k: int, numCookies: int)
  requires |a| == |b|
  requires |a| >= 1
  requires numCookies >= 1
  requires forall i :: 0 <= i < |a| ==> a[i] >= 1 && a[i] <= 1000000000
  requires forall i :: 0 <= i < |a| ==> b[i] >= 1 && b[i] <= 1000000000
  requires k >= 1 && k <= 1000000000
  requires a[0] * numCookies > b[0] + k
  ensures calculateDeficit(a, b, numCookies, 0) > k
{
  var needed := a[0] * numCookies;
  var deficit0 := needed - b[0];
  assert deficit0 > k;
  var currentDeficit := if needed > b[0] then needed - b[0] else 0;
  assert needed > b[0];
  assert currentDeficit == deficit0;
  assert calculateDeficit(a, b, numCookies, 0) == currentDeficit + calculateDeficit(a, b, numCookies, 1);
  deficitNonNegativeLemma(a, b, numCookies, 1);
  assert calculateDeficit(a, b, numCookies, 1) >= 0;
  assert calculateDeficit(a, b, numCookies, 0) >= currentDeficit;
  assert calculateDeficit(a, b, numCookies, 0) >= deficit0;
  assert calculateDeficit(a, b, numCookies, 0) > k;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>, b: seq<int>) returns (result: int)
  requires n >= 1 && n <= 100000
  requires k >= 1 && k <= 1000000000
  requires |a| == n && |b| == n
  requires forall i :: 0 <= i < n ==> a[i] >= 1 && a[i] <= 1000000000
  requires forall i :: 0 <= i < n ==> b[i] >= 1 && b[i] <= 1000000000
  ensures result >= 0
  ensures canMake(a, b, k, result)
  ensures !canMake(a, b, k, result + 1)
  ensures result <= 3000000000
// </vc-spec>
// <vc-code>
{
  var lo := 0;
  var hi := 3000000001;

  deficitZeroLemma(a, b, 0);
  assert canMake(a, b, k, 0);

  deficitLargeNumCookiesLemma(a, b, k, hi);
  assert !canMake(a, b, k, hi);

  while lo + 1 < hi
    invariant 0 <= lo < hi <= 3000000001
    invariant canMake(a, b, k, lo)
    invariant !canMake(a, b, k, hi)
  {
    var mid := (lo + hi) / 2;
    var canMakeResult := canMake(a, b, k, mid);
    if canMakeResult {
      lo := mid;
    } else {
      hi := mid;
    }
  }

  return lo;
}
// </vc-code>
