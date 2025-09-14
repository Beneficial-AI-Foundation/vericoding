// <vc-preamble>
function FilterDivisibleBy3(x: seq<int>): seq<int>
{
    seq(|x|, i requires 0 <= i < |x| => if x[i] % 3 == 0 then x[i] else 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed duplicate function and added helper lemma */function IsDivisibleBy3(n: int): bool {
    n % 3 == 0
}

lemma FilterPreservesDivisibleBy3(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures FilterDivisibleBy3(s)[i] == (if IsDivisibleBy3(s[i]) then s[i] else 0)
{
}

lemma FilterZeroPads(s: seq<int>)
    ensures |FilterDivisibleBy3(s)| == |s|
    && forall j: int :: 0 <= j < |s| ==> FilterDivisibleBy3(s)[j] == (if IsDivisibleBy3(s[j]) then s[j] else 0)
{
}
// </vc-helpers>

// <vc-spec>
method myfun4(x: seq<int>, y: seq<int>) returns (newY: seq<int>)
    requires |y| == 0
    ensures newY == FilterDivisibleBy3(x)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed sequence building logic */{
    newY := [];
    var i := 0;
    while i < |x|
        invariant 0 <= i <= |x|
        invariant |newY| == i
        invariant forall j: int :: 0 <= j < i ==> newY[j] == FilterDivisibleBy3(x)[j]
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
