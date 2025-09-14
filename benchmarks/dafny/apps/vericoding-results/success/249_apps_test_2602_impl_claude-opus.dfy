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
// No additional helpers needed
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
    // Check if we have enough total cookies
    if a + b < n + m {
        result := false;
        return;
    }
    
    // Check if we can satisfy all type-2 guests
    // Type-2 guests need one cookie of each type
    // So we need at least m cookies of each type available
    var minCookies := if a <= b then a else b;
    
    if m <= minCookies {
        result := true;
    } else {
        result := false;
    }
}
// </vc-code>

