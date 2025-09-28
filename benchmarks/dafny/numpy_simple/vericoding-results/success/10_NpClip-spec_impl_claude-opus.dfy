// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
    invariant forall j :: 0 <= j < i ==>
      if a[j] < min then result[j] == min
      else if a[j] > max then result[j] == max
      else result[j] == a[j]
  {
    if a[i] < min {
      result[i] := min;
    } else if a[i] > max {
      result[i] := max;
    } else {
      result[i] := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>
