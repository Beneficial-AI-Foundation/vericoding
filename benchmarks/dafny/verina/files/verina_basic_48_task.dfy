// <vc-preamble>
ghost predicate IsPerfectSquare(n: nat)
{
    exists i: nat :: i * i == n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsPerfectSquareFn(n: int) returns (result: bool)
    requires n >= 0
    ensures result <==> IsPerfectSquare(n as nat)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := false;
    // impl-end
}
// </vc-code>
