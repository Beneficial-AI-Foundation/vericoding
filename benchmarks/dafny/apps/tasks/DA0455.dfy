// <vc-preamble>
predicate ValidTestCase(a: nat, b: nat, n: nat, m: nat)
{
    n + m > 0
}

predicate CanSatisfyAllGuests(a: nat, b: nat, n: nat, m: nat)
{

    a + b >= n + m &&

    m <= min(a, b)
}

function min(x: nat, y: nat): nat
{
    if x <= y then x else y
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SolveCookieDistribution(a: nat, b: nat, n: nat, m: nat) returns (result: bool)
    requires ValidTestCase(a, b, n, m)
    ensures result == CanSatisfyAllGuests(a, b, n, m)
    ensures result ==> (a + b >= n + m && m <= min(a, b))
    ensures !result ==> (a + b < n + m || m > min(a, b))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
