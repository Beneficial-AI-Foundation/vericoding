predicate ValidInput(n: int, k: int)
{
    n >= 1 && k > 0
}

predicate IsCorrectResult(n: int, k: int, result: int)
    requires k > 0
{
    result > n && result % k == 0 && forall x :: n < x < result ==> x % k != 0
}

// <vc-helpers>
lemma ResultGreaterThanN(n: int, k: int, result: int)
  requires ValidInput(n, k)
  requires k > 0
  requires if n % k == 0 then result == n + k else result == (n / k + 1) * k
  ensures result > n
{}

lemma ResultDivisibleByK(n: int, k: int, result: int)
  requires k > 0
  requires if n % k == 0 then result == n + k else result == (n / k + 1) * k
  ensures result % k == 0
{}

lemma NoOtherMultipleBetween(n: int, k: int, result: int)
  requires ValidInput(n, k)
  requires k > 0
  requires if n % k == 0 then result == n + k else result == (n / k + 1) * k
  requires result > n && result % k == 0
  ensures forall x :: n < x < result ==> x % k != 0
{
  var prev := (n / k) * k;
  if n % k == 0 {
    forall x | n < x < result
      ensures x % k != 0
    {
      if prev < x < result && x % k == 0 {
        // contradiction since result is next multiple after prev
      }
    }
  } else {
    forall x | n < x < result
      ensures x % k != 0
    {
      // since result is the next multiple after (n / k) * k
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
// </vc-spec>
// <vc-code>
{
  var res;
  if n % k == 0 {
    res := n + k;
  } else {
    res := ((n / k) + 1) * k;
  }
  ResultGreaterThanN(n, k, res);
  ResultDivisibleByK(n, k, res);
  NoOtherMultipleBetween(n, k, res);
  return res;
}
// </vc-code>

