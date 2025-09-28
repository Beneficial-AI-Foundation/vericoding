// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function clamp(x: int, min: int, max: int): int
  ensures min <= max ==> min <= clamp(x, min, max) <= max
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
  var r := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant r.Length == a.Length
    invariant forall j :: 0 <= j < i ==> (if a[j] < min then r[j] == min else if a[j] > max then r[j] == max else r[j] == a[j])
  {
    var v := a[i];
    if v < min {
      r[i] := min;
    } else if v > max {
      r[i] := max;
    } else {
      r[i] := v;
    }
    i := i + 1;
  }
  result := r;
}
// </vc-code>
