predicate ValidTestCase(a: nat, b: nat, n: nat, m: nat)
{
    n + m > 0
}

predicate CanSatisfyAllGuests(a: nat, b: nat, n: nat, m: nat)
{
    // First check: must have enough total cookies
    a + b >= n + m &&
    // Second check: type-2 guests are the limiting factor
    // They will take from the minority cookie type, so we need
    // enough of the minority type to satisfy all type-2 guests
    m <= min(a, b)
}

function min(x: nat, y: nat): nat
{
    if x <= y then x else y
}

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
    result := (a + b >= n + m) && (m <= min(a, b));
}
// </vc-code>

