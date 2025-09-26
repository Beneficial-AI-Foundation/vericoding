// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Max(a: int, b:int) returns (c: int)
    ensures c >= a && c>= b
// </vc-spec>
// <vc-code>
{
    if (a < b)
        { c := b; }
    else
        { c := a; }
    assert a <= c && b <= c;
}
// </vc-code>
