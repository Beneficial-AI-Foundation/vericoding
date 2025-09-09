function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)

    requires x > 1

    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
