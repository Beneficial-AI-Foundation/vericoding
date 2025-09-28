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
/* code modified by LLM (iteration 4): implemented arange logic */
{
  var len := ArangeLength(start, stop, step);
  result := new int[len];
  result[0] := start;
  var i := 1;
  while i < len
    invariant 0 <= i <= len
    invariant result[0] == start
    invariant forall j | 1 <= j < i :: result[j] == result[j-1] + step
  {
    result[i] := result[i-1] + step;
    i := i + 1;
  }
}
// </vc-code>
