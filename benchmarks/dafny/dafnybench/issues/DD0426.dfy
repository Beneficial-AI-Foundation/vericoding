// <vc-preamble>
//Problem 01
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method sumOdds(n: nat) returns (sum: nat)
    requires n > 0;
    ensures sum == n * n;
// </vc-spec>
// <vc-code>
{
    sum := 1;
    var i := 0;

    while i < n-1
        invariant 0 <= i < n;
        invariant sum == (i + 1) * (i + 1);
    {
        i := i + 1;
        sum := sum + 2 * i + 1;
    }

    assert sum == n * n;
}
// </vc-code>

//problem02
//a)