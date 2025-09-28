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
  /* code modified by LLM (iteration 3): Replaced for loop with while loop to fix bounds error, ensuring safe iteration and postcondition proof */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall k :: 0 <= k < i ==> 
      (if a[k] < min then result[k] == min 
       else if a[k] > max then result[k] == max 
       else result[k] == a[k])
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
