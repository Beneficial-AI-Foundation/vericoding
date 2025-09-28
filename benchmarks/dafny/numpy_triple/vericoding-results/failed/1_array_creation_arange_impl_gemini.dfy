// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added Ceil function for reals */
function Ceil(r: real): int
{
  var i := r as int;
  if r == i as real then i
  else if r > 0.0 then i + 1
  else i
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
  /* code modified by LLM (iteration 5): pre-calculated size and used integer-based loop */
  result := [];
  if step > 0.0 {
    if start < stop {
      var num := (stop - start) / step;
      var size := Ceil(num);
      
      while |result| < size
        invariant 0 <= |result| <= size
        invariant forall j :: 0 <= j < |result| ==> result[j] == start + (j as real) * step
        invariant forall j :: 0 <= j < |result| ==> result[j] >= start && result[j] < stop
        decreases size - |result|
      {
        result := result + [start + (|result| as real) * step];
      }
    }
  } else { // step < 0.0
    if start > stop {
      var num := (stop - start) / step;
      var size := Ceil(num);
      
      while |result| < size
        invariant 0 <= |result| <= size
        invariant forall j :: 0 <= j < |result| ==> result[j] == start + (j as real) * step
        invariant forall j :: 0 <= j < |result| ==> result[j] <= start && result[j] > stop
        decreases size - |result|
      {
        result := result + [start + (|result| as real) * step];
      }
    }
  }
}
// </vc-code>
