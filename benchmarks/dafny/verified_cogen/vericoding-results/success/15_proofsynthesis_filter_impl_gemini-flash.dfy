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
    newY := [];
    var i := 0;
    while i < |x|
        invariant 0 <= i <= |x|
        invariant |newY| == i
        invariant forall k :: 0 <= k < i ==> newY[k] == (if x[k] % 3 == 0 then x[k] else 0)
    {
        if x[i] % 3 == 0 {
            newY := newY + [x[i]];
        } else {
            newY := newY + [0];
        }
        i := i + 1;
    }
}
// </vc-code>
