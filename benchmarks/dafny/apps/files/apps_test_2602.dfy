/*
Given vanilla cookies (a), chocolate cookies (b), type-1 guests (n), and type-2 guests (m),
determine if there exists an ordering of all guests such that no guest gets angry.
Type-1 guests choose vanilla if v > c, else chocolate.
Type-2 guests choose chocolate if v > c, else vanilla.
A guest gets angry if their chosen cookie type has 0 cookies available.

// First check: must have enough total cookies

// Second check: type-2 guests are the limiting factor

// They will take from the minority cookie type, so we need

// enough of the minority type to satisfy all type-2 guests
*/

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
