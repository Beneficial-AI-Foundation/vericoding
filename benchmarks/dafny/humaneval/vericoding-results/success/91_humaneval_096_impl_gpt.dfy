// <vc-preamble>

predicate is_prime_number(num: int)
{
    num >= 2 && forall k :: 2 <= k < num ==> num % k != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): retain simple alias to the prime predicate for readability */
function isPrimeAlias(num: int): bool { is_prime_number(num) }
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
  /* code modified by LLM (iteration 3): enumerate primes below n while maintaining sortedness and completeness via invariants */
  result := [];
  var p := 0;
  while p < n
    invariant 0 <= p
    invariant forall i :: 0 <= i < |result| ==> is_prime_number(result[i])
    invariant forall i :: 0 <= i < |result| ==> result[i] < p
    invariant forall i :: 0 <= i < |result| ==> result[i] < n
    invariant forall q :: 2 <= q < p && is_prime_number(q) ==> q in result
    invariant forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    decreases n - p
  {
    if p >= 2 && is_prime_number(p) {
      result := result + [p];
    }
    p := p + 1;
  }
}
// </vc-code>
