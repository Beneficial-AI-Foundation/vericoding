// <vc-preamble>
function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed as prime function is already defined */
// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)

    requires x > 1

    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Implemented prime factorization to count prime factors with multiplicity, fixed termination issues with proper decreases clauses */
  var count: nat := 0;
  var m: nat := x;
  var p: nat := 2;
  while p * p <= m decreases m, p
  {
    if m % p == 0 {
      while m % p == 0 decreases m
      {
        m := m / p;
        count := count + 1;
      }
    }
    p := if p == 2 then 3 else p + 2;
  }
  if m > 1 {
    count := count + 1;
  }
  ans := count == 3;
}
// </vc-code>
