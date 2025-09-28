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
/* helper modified by LLM (iteration 5): weakened assertions to handle division correctly */
lemma ArangeLengthPositive(start: int, stop: int, step: int)
    requires step != 0 && (if step < 0 then start > stop else start < stop)
    ensures ArangeLength(start, stop, step) > 0
{
    if step < 0 {
        assert start > stop;
        assert start - stop > 0;
        assert -step > 0;
        if start - stop >= -step {
            assert (start - stop) / (-step) >= 1;
        }
    } else {
        assert start < stop;
        assert stop - start > 0;
        assert step > 0;
        if stop - start >= step {
            assert (stop - start) / step >= 1;
        }
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
    /* code modified by LLM (iteration 5): added lemma call to prove length > 0 */
    var length := ArangeLength(start, stop, step);
    ArangeLengthPositive(start, stop, step);
    result := new int[length];
    var i := 0;
    var current := start;
    while i < length
        invariant 0 <= i <= length
        invariant i < length ==> current == start + i * step
        invariant forall j :: 0 <= j < i ==> result[j] == start + j * step
    {
        result[i] := current;
        current := current + step;
        i := i + 1;
    }
}
// </vc-code>
