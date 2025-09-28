// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified length calculation with proper bounds */
function ComputeLength(start: real, stop: real, step: real): nat
  requires step != 0.0
{
  if step > 0.0 then
    if start >= stop then 0
    else var diff := stop - start;
         var exactLength := diff / step;
         exactLength.Floor as nat + 1
  else
    if start <= stop then 0
    else var diff := start - stop;
         var exactLength := diff / (-step);
         exactLength.Floor as nat + 1
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
  /* code modified by LLM (iteration 5): direct calculation with proper bounds checking */
  if step > 0.0 {
    if start >= stop {
      result := [];
    } else {
      var diff := stop - start;
      var exactLength := diff / step;
      var maxLength := exactLength.Floor as nat + 1;
      
      result := [];
      var i := 0;
      while i < maxLength
        invariant 0 <= i <= maxLength
        invariant |result| == i
        invariant forall j :: 0 <= j < |result| ==> result[j] == start + (j as real) * step
        invariant forall j :: 0 <= j < |result| ==> result[j] >= start && result[j] < stop
      {
        var value := start + (i as real) * step;
        if value < stop {
          result := result + [value];
        } else {
          break;
        }
        i := i + 1;
      }
    }
  } else {
    if start <= stop {
      result := [];
    } else {
      var diff := start - stop;
      var exactLength := diff / (-step);
      var maxLength := exactLength.Floor as nat + 1;
      
      result := [];
      var i := 0;
      while i < maxLength
        invariant 0 <= i <= maxLength
        invariant |result| == i
        invariant forall j :: 0 <= j < |result| ==> result[j] == start + (j as real) * step
        invariant forall j :: 0 <= j < |result| ==> result[j] <= start && result[j] > stop
      {
        var value := start + (i as real) * step;
        if value > stop {
          result := result + [value];
        } else {
          break;
        }
        i := i + 1;
      }
    }
  }
}
// </vc-code>
