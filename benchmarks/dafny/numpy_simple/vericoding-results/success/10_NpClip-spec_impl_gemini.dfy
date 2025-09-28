// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function clip_value(v: int, min_val: int, max_val: int): int
    requires min_val < max_val
{
    if v < min_val then min_val
    else if v > max_val then max_val
    else v
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
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == clip_value(a[j], min, max)
  {
    result[i] := clip_value(a[i], min, max);
    i := i + 1;
  }
}
// </vc-code>
