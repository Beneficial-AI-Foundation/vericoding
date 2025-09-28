// <vc-preamble>
function ArangeLength(start: int, stop: int, step: int): nat
{
    if step != 0 then
        if step < 0 then
            if start > stop then
                (start - stop) / (-step)
            else
                0
        else
            if start < stop then
                (stop - start) / step
            else
                0
    else
        0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added case split to guide verifier */
lemma ArangeBoundsHelper(start: int, stop: int, step: int, i: int)
    requires step != 0
    requires if step > 0 then start < stop else start > stop
    requires 0 <= i < ArangeLength(start, stop, step)
    ensures if step > 0 then start + i * step < stop
            else start + i * step > stop
{
    if step > 0 {
    } else {
    }
}
// </vc-helpers>

// <vc-spec>
method Arange(start: int, stop: int, step: int) returns (result: array<int>)
    requires 
        step != 0 &&
        (if step < 0 then start > stop else start < stop)
    ensures
        result.Length == ArangeLength(start, stop, step) &&
        result.Length > 0 &&
        result[0] == start
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): resubmitting correct loop implementation */
    var len := ArangeLength(start, stop, step);
    result := new int[len];
    var i := 0;
    while i < len
        invariant 0 <= i <= len
        invariant forall j :: 0 <= j < i ==> result[j] == start + j * step
        invariant forall j :: 0 <= j < i ==> (if step > 0 then start + j * step < stop else start + j * step > stop)
    {
        ArangeBoundsHelper(start, stop, step, i);
        result[i] := start + i * step;
        i := i + 1;
    }
}
// </vc-code>
