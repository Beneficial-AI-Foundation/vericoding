function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

// <vc-helpers>
predicate isPrime(n: int) {
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

predicate allPrime(factors: seq<int>) {
  forall i :: 0 <= i < |factors| ==> isPrime(factors[i])
}

predicate sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma ProdPositive(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures prod(s) > 0
{
  if |s| == 0 {
  } else {
    ProdPositive(s[..|s|-1]);
  }
}

lemma ProdDivisibility(s: seq<int>, factor: int)
  requires factor > 0
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures prod(s + [factor]) == prod(s) * factor
{
  if |s + [factor]| == 1 {
    assert s == [];
    assert prod(s) == 1;
  } else {
    assert (s + [factor])[..|s + [factor]| - 1] == s;
    assert (s + [factor])[|s + [factor]| - 1] == factor;
  }
}

lemma CandidatePrime(n: int, candidate: int)
  requires n > 1
  requires candidate >= 2
  requires forall p :: isPrime(p) && p < candidate ==> n % p != 0
  requires n % candidate == 0
  ensures isPrime(candidate)
{
  if candidate > 1 {
    forall k | 2 <= k < candidate
      ensures candidate % k != 0
    {
      if candidate % k == 0 {
        assert n % k == 0;
        if isPrime(k) {
          assert k < candidate;
          assert n % k != 0;
          assert false;
        } else {
          var j :| 2 <= j < k && k % j == 0;
          assert candidate % j == 0;
          assert n % j == 0;
          if isPrime(j) {
            assert j < candidate;
            assert n % j != 0;
            assert false;
          }
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def factorize(n: int) -> List[int]
Return list of prime factors of given integer in the order from smallest to largest. Each of the factors should be listed number of times corresponding to how many times it appeares in factorization. Input number should be equal to the product of all factors
*/
// </vc-description>

// <vc-spec>
method factorize(n: int) returns (factors: seq<int>)
  requires n >= 1
  ensures allPrime(factors)
  ensures sorted(factors)
  ensures prod(factors) == n
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    factors := [];
    return;
  }
  
  factors := [];
  var remaining := n;
  var candidate := 2;
  
  while remaining > 1
    invariant remaining >= 1
    invariant candidate >= 2
    invariant allPrime(factors)
    invariant sorted(factors)
    invariant prod(factors) * remaining == n
    invariant forall p :: isPrime(p) && p < candidate ==> remaining % p != 0
    invariant |factors| == 0 ==> candidate == 2
    invariant |factors| > 0 ==> factors[|factors|-1] <= candidate
    decreases remaining, candidate
  {
    if remaining % candidate == 0 {
      CandidatePrime(remaining, candidate);
      
      factors := factors + [candidate];
      ProdDivisibility(factors[..|factors|-1], candidate);
      
      remaining := remaining / candidate;
      candidate := 2;
    } else {
      candidate := candidate + 1;
    }
  }
}
// </vc-code>
