// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method main(x :int) returns (j :int, i :int)
requires x > 0
ensures j == 2 * x
// </vc-spec>
// <vc-code>
{
    i := 0;
    j := 0;

    while i < x
        invariant 0 <= i <= x
        invariant j == 2 * i
    {
        j := j + 2;
        i := i + 1;
    }
}
// </vc-code>
