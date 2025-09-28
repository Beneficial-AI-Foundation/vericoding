// <vc-preamble>
predicate ValidInput(n: int, s: int, v: seq<int>)
{
    n > 0 && |v| == n && s >= 0 && forall i :: 0 <= i < |v| ==> v[i] >= 0
}

function sum(v: seq<int>): int
{
    if |v| == 0 then 0
    else v[0] + sum(v[1..])
}

function minSeq(v: seq<int>): int
    requires |v| > 0
    ensures (forall i :: 0 <= i < |v| ==> v[i] >= 0) ==> minSeq(v) >= 0
{
    if |v| == 1 then v[0]
    else if v[0] <= minSeq(v[1..]) then v[0]
    else minSeq(v[1..])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed redundant min function as it is already defined in preamble. */
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: int, v: seq<int>) returns (result: int)
    requires ValidInput(n, s, v)
    ensures sum(v) < s ==> result == -1
    ensures sum(v) >= s ==> result == min((sum(v) - s) / n, minSeq(v))
    ensures result == -1 || result >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implemented the logic to calculate the result based on sum(v) compared to s. */
{
    var totalSum := sum(v);
    if totalSum < s {
        result := -1;
    } else {
        var minPossibleValue := (totalSum - s) / n;
        var actualMinValue := minSeq(v);
        result := min(minPossibleValue, actualMinValue);
    }
}
// </vc-code>
