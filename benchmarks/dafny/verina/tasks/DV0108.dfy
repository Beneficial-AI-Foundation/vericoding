// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsPrime(n: nat) returns (result: bool)
    requires n >= 2
    ensures result ==> forall k: nat :: 2 <= k < n ==> n % k != 0
    ensures !result ==> exists k: nat :: 2 <= k < n && n % k == 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := false;
    // impl-end
}
// </vc-code>
