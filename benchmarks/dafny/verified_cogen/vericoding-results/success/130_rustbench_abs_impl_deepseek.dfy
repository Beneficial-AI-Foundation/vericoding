// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function abs_val(x: int): int { if x >= 0 then x else -x }
// </vc-helpers>

// <vc-spec>
method Abs(x: int) returns (result: int)
    requires x != -2147483648
    ensures result >= 0
    ensures result == x || result == -x
// </vc-spec>
// <vc-code>
{
  result := abs_val(x);
}
// </vc-code>
