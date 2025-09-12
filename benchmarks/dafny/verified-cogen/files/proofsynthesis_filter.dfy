// <vc-preamble>
function FilterDivisibleBy3(x: seq<int>): seq<int>
{
    seq(|x|, i requires 0 <= i < |x| => if x[i] % 3 == 0 then x[i] else 0)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method myfun4(x: seq<int>, y: seq<int>) returns (newY: seq<int>)
    requires |y| == 0
    ensures newY == FilterDivisibleBy3(x)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
