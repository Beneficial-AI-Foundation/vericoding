// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function computeLengthHelper(start: real, stop: real, step: real): (length: int)
  requires step != 0.0
  ensures length >= 0
  ensures step > 0.0 && start < stop ==> length == ((stop - start - step) / step).Floor as int + 1
  ensures step < 0.0 && start > stop ==> length == ((start - stop + step) / (-step)).Floor as int + 1
  ensures (step > 0.0 && start >= stop) || (step < 0.0 && start <= stop) ==> length == 0
{
  if step > 0.0 then
    if start < stop then
      ((stop - start) / step).Floor as int
    else
      0
  else
    if start > stop then
      ((start - stop) / (-step)).Floor as int
    else
      0
}
// </vc-helpers>

// <vc-spec>
method Arange(start: real, stop: real, step: real) returns (result: seq<real>)
  requires step != 0.0
  ensures step > 0.0 ==> (|result| == 0 <==> start >= stop)
  ensures step < 0.0 ==> (|result| == 0 <==> start <= stop)
  ensures step > 0.0 && start < stop ==> 
    |result| > 0 && |result| as real * step >= (stop - start) && (|result| - 1) as real * step < (stop - start)
  ensures step < 0.0 && start > stop ==> 
    |result| > 0 && |result| as real * (-step) >= (start - stop) && (|result| - 1) as real * (-step) < (start - stop)
  ensures forall i :: 0 <= i < |result| ==> result[i] == start + (i as real) * step
  ensures step > 0.0 ==> forall i :: 0 <= i < |result| ==> result[i] >= start && result[i] < stop
  ensures step < 0.0 ==> forall i :: 0 <= i < |result| ==> result[i] <= start && result[i] > stop
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed Ceil to Floor in helper and adjusted length computation */
  var length := computeLengthHelper(start, stop, step);
  result := [];
  
  var i: int := 0;
  while i < length
    invariant 0 <= i <= length
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == start + (j as real) * step
  {
    result := result + [start + (i as real) * step];
    i := i + 1;
  }
}
// </vc-code>
