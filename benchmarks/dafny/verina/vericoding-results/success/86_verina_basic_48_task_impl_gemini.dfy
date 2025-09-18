// <vc-preamble>
ghost predicate IsPerfectSquare(n: nat)
{
    exists i: nat :: i * i == n
}
// </vc-preamble>

// <vc-helpers>
lemma SqrtCorrectness(n: nat, i: nat)
    requires i * i >= n
    requires forall j: nat :: j < i ==> j * j < n
    ensures (i * i == n) <==> IsPerfectSquare(n)
{
    if i * i != n {
        assert i * i > n;
        forall k: nat | k * k == n
            ensures false
        {
            if k < i {
                assert k * k < n;
            } else {
                assert k * k >= i * i;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method IsPerfectSquareFn(n: int) returns (result: bool)
    requires n >= 0
    ensures result <==> IsPerfectSquare(n as nat)
// </vc-spec>
// <vc-code>
{
    var i: nat := 0;
    while i * i < n as nat
        invariant forall j: nat :: j < i ==> j * j < n as nat
    {
        i := i + 1;
    }
    SqrtCorrectness(n as nat, i);
    result := (i * i == n as nat);
}
// </vc-code>
