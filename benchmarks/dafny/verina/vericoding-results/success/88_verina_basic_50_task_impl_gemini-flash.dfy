// <vc-preamble>
function abs(x: int): int
{
    if x >= 0 then x else -x
}
// </vc-preamble>

// <vc-helpers>
function abs_ensures(x: int, result: int): bool
{
    (x >= 0 ==> result == x) && (x < 0 ==> x + result == 0)
}
// </vc-helpers>

// <vc-spec>
method abs_impl(x: int) returns (result: int)
    ensures (x >= 0 ==> result == x) && (x < 0 ==> x + result == 0)
// </vc-spec>
// <vc-code>
{
    if x >= 0 {
        result := x;
    } else {
        result := -x;
    }
    assert abs_ensures(x, result);
}
// </vc-code>
