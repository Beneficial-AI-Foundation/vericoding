// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Ceil(x: real): int
  requires x >= 0.0
  ensures Ceil(x) as real >= x
  ensures (Ceil(x) - 1) as real < x
{
  if (x as int) as real == x then x as int else (x as int) + 1
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
  if step > 0.0
  {
    if start >= stop
    {
      return [];
    }
    else
    {
      var n := Ceil((stop - start) / step);
      var seq := [];
      for i := 0 to n
      {
        seq := seq + [start + i * step];
      }
      return seq;
    }
  }
  else
  {
    if start <= stop
    {
      return [];
    }
    else
    {
      var n := Ceil((start - stop) / (-step));
      var seq := [];
      for i := 0 to n
      {
        seq := seq + [start + i * step];
      }
      return seq;
    }
  }
}
// </vc-code>
