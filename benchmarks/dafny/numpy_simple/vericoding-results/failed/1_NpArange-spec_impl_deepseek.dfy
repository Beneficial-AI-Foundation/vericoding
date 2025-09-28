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
/* helper modified by LLM (iteration 5): Fixed assertions with division properties and exact bounds */
function ArangeElement(i: int, start: int, step: int): int { start + i * step }

lemma ArangeStartValid(start: int, stop: int, step: int)
    requires step != 0 && (if step < 0 then start > stop else start < stop)
    ensures 0 < ArangeLength(start, stop, step) && start == ArangeElement(0, start, step)
{
    if step > 0 {
        assert start < stop;
        var n := (stop - start) / step;
        assert n * step <= stop - start < (n + 1) * step;
    } else {
        assert start > stop;
        var n := (start - stop) / (-step);
        assert n * (-step) <= start - stop < (n + 1) * (-step);
    }
    assert ArangeElement(0, start, step) == start + 0 * step == start;
}

lemma ArangeFinalBoundary(start: int, stop: int, step: int)
    requires step != 0 && (if step < 0 then start > stop else start < stop)
    ensures if step > 0 then ArangeElement(ArangeLength(start, stop, step) - 1, start, step) < stop 
            else ArangeElement(ArangeLength(start, stop, step) - 1, start, step) > stop
{
    var len := ArangeLength(start, stop, step);
    var last := ArangeElement(len - 1, start, step);
    
    if step > 0 {
        assert len == (stop - start) / step;
        assert (stop - start) % step >= 0;
        assert last == start + (len - 1) * step;
        assert last + step == start + len * step;
        assert last + step <= stop;
        assert last < stop;
    } else {
        var absStep := -step;
        assert len == (start - stop) / absStep;
        assert (start - stop) % absStep >= 0;
        assert last == start + (len - 1) * step;
        assert last + step == start + len * step;
        assert last + step >= stop;
        assert last > stop;
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
  /* code modified by LLM (iteration 5): Updated with proper lemma calls */
  ArangeStartValid(start, stop, step);
  var length := ArangeLength(start, stop, step);
  result := new int[length];
  
  var i := 0;
  while i < length
    invariant 0 <= i <= length
    invariant forall j :: 0 <= j < i ==> result[j] == start + j * step
  {
    result[i] := start + i * step;
    i := i + 1;
  }
}
// </vc-code>
