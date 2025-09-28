// <vc-preamble>

predicate is_prime_number(num: int)
{
    num >= 2 && forall k :: 2 <= k < num ==> num % k != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method count_up_to(n: int) returns (result: seq<int>)
    requires n >= 0
    ensures forall i :: 0 <= i < |result| ==> is_prime_number(result[i])
    ensures forall i :: 0 <= i < |result| ==> result[i] < n
    ensures forall p :: 2 <= p < n && is_prime_number(p) ==> p in result
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Added guard for n <2, adjusted inner loop invariant for non-prime case */
  if n < 2 {
    result := [];
  } else {
    var primes: seq<int> := [];
    var i := 2;
    while i < n
      invariant 2 <= i <= n
      invariant forall j :: 0 <= j < |primes| ==> is_prime_number(primes[j])
      invariant forall j :: 0 <= j < |primes| ==> primes[j] < i
      invariant forall p :: 2 <= p < i && is_prime_number(p) ==> p in primes
      invariant forall j, k :: 0 <= j < k < |primes| ==> primes[j] < primes[k]
    {
      var is_prime_local := true;
      var k := 2;
      while k < i && is_prime_local
        invariant 2 <= k <= i
        invariant is_prime_local ==> forall m :: 2 <= m < k ==> i % m != 0
        invariant !is_prime_local ==> exists m :: 2 <= m < k && i % m == 0
      {
        if i % k == 0 {
          is_prime_local := false;
        }
        k := k + 1;
      }
      if is_prime_local {
        primes := primes + [i];
      }
      i := i + 1;
    }
    result := primes;
  }
}
// </vc-code>
