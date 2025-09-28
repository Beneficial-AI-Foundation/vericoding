// <vc-preamble>
function FilterDivisibleBy3(x: seq<int>): seq<int>
{
    seq(|x|, i requires 0 <= i < |x| => if x[i] % 3 == 0 then x[i] else 0)
}
// </vc-preamble>

// <vc-helpers>
lemma Filter3AppendLemma(s: seq<int>, item: int)
  ensures FilterDivisibleBy3(s + [item]) == FilterDivisibleBy3(s) + [if item % 3 == 0 then item else 0]
{}
// </vc-helpers>

// <vc-spec>
method myfun4(x: seq<int>, y: seq<int>) returns (newY: seq<int>)
    requires |y| == 0
    ensures newY == FilterDivisibleBy3(x)
// </vc-spec>
// <vc-code>
{
    newY := [];
    var i: nat := 0;
    while i < |x|
        invariant i <= |x|
        invariant newY == FilterDivisibleBy3(x[..i])
    {
        newY := newY + [if x[i] % 3 == 0 then x[i] else 0];
        i := i + 1;
    }
}
// </vc-code>
