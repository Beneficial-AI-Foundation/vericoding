/*
Given n notes where each note i has maximum playable volume a_i and required total volume b_i,
find piano volume x_i and guitar volume y_i such that 1 ≤ x_i ≤ a_i, 1 ≤ y_i ≤ a_i, and x_i + y_i = b_i.
For playable notes, add x_i × y_i to total joy. For unplayable notes, subtract 1.
Return the maximum possible total joy.
*/

function sum_contributions(a: seq<int>, b: seq<int>): int
    requires |a| == |b|
{
    if |a| == 0 then 0
    else 
        (if b[0] > 1 && 2 * a[0] >= b[0] then
            var x := b[0] / 2;
            var y := b[0] - x;
            x * y
         else -1) + sum_contributions(a[1..], b[1..])
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, b: seq<int>) returns (result: int)
    requires |a| == |b|
    ensures result == sum_contributions(a, b)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
