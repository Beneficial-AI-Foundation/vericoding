// <vc-preamble>
predicate isPrime(n: int)
{
    n >= 2 && forall k :: 2 <= k < n ==> n % k != 0
}

function product(factors: seq<int>): int
{
    if |factors| == 0 then 1
    else factors[0] * product(factors[1..])
}

predicate isNonDecreasing(factors: seq<int>)
{
    forall i, j :: 0 <= i < j < |factors| ==> factors[i] <= factors[j]
}
lemma ProductAppend(factors: seq<int>, x: int)
    ensures product(factors + [x]) == product(factors) * x
{
    if |factors| == 0 {
        assert factors + [x] == [x];
        assert product([x]) == x * product([]) == x * 1 == x;
        assert product(factors) * x == 1 * x == x;
    } else {
        assert (factors + [x])[0] == factors[0];
        assert (factors + [x])[1..] == factors[1..] + [x];
        ProductAppend(factors[1..], x);
        assert product(factors[1..] + [x]) == product(factors[1..]) * x;
        assert product(factors + [x]) == factors[0] * product(factors[1..] + [x]);
        assert product(factors + [x]) == factors[0] * product(factors[1..]) * x;
        assert product(factors + [x]) == product(factors) * x;
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method factorize(n: int) returns (factors: seq<int>)
    ensures n <= 1 ==> |factors| == 0
    ensures n > 1 ==> product(factors) == n
    ensures forall i :: 0 <= i < |factors| ==> isPrime(factors[i])
    ensures isNonDecreasing(factors)
    ensures forall i :: 0 <= i < |factors| ==> factors[i] >= 2
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added decreases clause and fixed invariant maintenance */
  factors := [];
  if n <= 1 {
    return;
  }
  
  var remaining := n;
  var candidate := 2;
  
  while remaining > 1
    decreases remaining + candidate
    invariant candidate >= 2
    invariant remaining >= 1
    invariant product(factors) * remaining == n
    invariant forall i :: 0 <= i < |factors| ==> factors[i] >= 2
    invariant forall i :: 0 <= i < |factors| ==> factors[i] <= remaining
    invariant isNonDecreasing(factors)
    invariant |factors| > 0 ==> factors[|factors|-1] <= candidate
  {
    // Check if candidate divides remaining
    if remaining % candidate == 0 {
      // Check if candidate is prime
      var isPrimeCand := true;
      var k := 2;
      while k < candidate
        decreases candidate - k
        invariant 2 <= k <= candidate
        invariant isPrimeCand <==> forall j :: 2 <= j < k ==> candidate % j != 0
      {
        if candidate % k == 0 {
          isPrimeCand := false;
          break;
        }
        k := k + 1;
      }
      
      if isPrimeCand && candidate >= 2 {
        ProductAppend(factors, candidate);
        factors := factors + [candidate];
        remaining := remaining / candidate;
      } else {
        candidate := candidate + 1;
      }
    } else if candidate * candidate > remaining {
      // remaining must be prime if no divisors up to sqrt(remaining)
      if remaining > 1 {
        // Verify remaining is prime
        var isPrimeRem := true;
        var m := 2;
        while m < remaining
          decreases remaining - m
          invariant 2 <= m <= remaining
          invariant isPrimeRem <==> forall j :: 2 <= j < m ==> remaining % j != 0
        {
          if remaining % m == 0 {
            isPrimeRem := false;
            break;
          }
          m := m + 1;
        }
        
        if isPrimeRem && remaining >= 2 {
          ProductAppend(factors, remaining);
          factors := factors + [remaining];
          remaining := 1;
        } else {
          candidate := candidate + 1;
        }
      }
    } else {
      candidate := candidate + 1;
    }
  }
}
// </vc-code>
