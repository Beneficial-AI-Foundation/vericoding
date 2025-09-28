// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): ClipVal ensures bounded and matches clipping */
function ClipVal(x: int, min: int, max: int): int
  requires min < max
  ensures min <= ClipVal(x,min,max) <= max
  ensures ClipVal(x,min,max) == x || ClipVal(x,min,max) == min || ClipVal(x,min,max) == max
{
  if x < min then min else if x > max then max else x
}
// </vc-helpers>

// <vc-spec>
method Clip(a: array<int>, min: int, max: int) returns (result: array<int>)
    requires min < max
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> 
        if a[i] < min then result[i] == min
        else if a[i] > max then result[i] == max
        else result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement Clip using ClipVal */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == ClipVal(a[j], min, max)
    invariant result.Length == a.Length
  {
    var v := ClipVal(a[i], min, max);
    result[i] := v;
    i := i + 1;
  }
}
// </vc-code>
