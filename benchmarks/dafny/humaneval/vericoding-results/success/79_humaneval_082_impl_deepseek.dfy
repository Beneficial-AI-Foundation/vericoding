// <vc-preamble>

predicate is_prime_number(n: int)
{
    n >= 2 && (forall k :: 2 <= k < n ==> n % k != 0)
}
// </vc-preamble>

// <vc-helpers>
function get_length(s: string): int {
  |s|
}

lemma length_property(s: string)
  ensures |s| >= 0
{
}

lemma prime_length_lemma(n: int)
  requires n >= 2
  ensures is_prime_number(n) <==> (forall k :: 2 <= k < n ==> n % k != 0)
{
}

/* helper modified by LLM (iteration 3): Added lemma to prove prime check equivalence */
// </vc-helpers>

// <vc-spec>
method prime_length(s: string) returns (result: bool)
    ensures result <==> is_prime_number(|s|)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Simplified implementation using helper lemma and direct return */
  var len: int := |s|;
  if len < 2 {
    result := false;
  } else {
    result := (forall k :: 2 <= k < len ==> len % k != 0);
  }
}
// </vc-code>
