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
{
  if n % k == 0 {
    // result = n + k > n
  } else {
    var q := n / k;
    var r := n % k;
    calc {
      result;
    == (q + 1) * k;
    == q * k + k;
    == n - r + k;
    >= n + 1;
    > n;
    }
  }
}

lemma ResultDivisibleByK(n: int, k: int, result: int)
  requires k > 0
  requires if n % k == 0 then result == n + k else result == (n / k + 1) * k
  ensures result % k == 0
{
  if n % k == 0 {
    // result = n + k ≡ n % k + 0 ≡ 0
  } else {
    var q := n / k;
    // n = q * k + r where 0 < r < k
    calc {
      result;
    == (q + 1) * k;
    ≡ 0 mod k;
    }
  }
}

lemma NoOtherMultipleBetween(n: int, k: int, result: int)
  requires ValidInput(n, k)
  requires k > 0
  requires if n % k == 0 then result == n + k else result == (n / k + 1) * k
  requires result > n && result % k == 0
  ensures forall x :: n < x < result ==> x % k != 0
{
  var prev := (n / k) * k;
  if n % k == 0 {
    // prev == n, result == n + k
    forall x | n < x < n + k
      ensures x % k != 0
    {
      calc {
        x % k;
      == 0; // assume for contradiction
      {
        // x = n + d where 0 < d < k, but x % k == 0 implies d % k == 0
        // but d < k and d > 0, so d = 0, contradiction
      }
      }
    }
  } else {
    // prev = (n / k) * k < n since n % k != 0
    // result = prev + k
    // The next multiple after prev is prev + k = result
    forall x | n < x < prev + k
      ensures x % k != 0
    {
      calc {
        x % k;
      == 0; // contradiction
      {
        // Since prev is the largest multiple <= prev
        // Next is prev + k, which is result, not in (n, result)
        // So no multiples in between
      }
      }
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

