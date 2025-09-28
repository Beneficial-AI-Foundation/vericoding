// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function clipValue(x: int, minVal: int, maxVal: int): int
  requires minVal < maxVal
{
  if x < minVal then minVal
  else if x > maxVal then maxVal
  else x
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
    invariant forall j :: 0 <= j < i ==> result[j] == clipValue(a[j], min, max)
  {
    result[i] := clipValue(a[i], min, max);
    i := i + 1;
  }
}
// </vc-code>
