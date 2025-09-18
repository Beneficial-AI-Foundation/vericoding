// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function compute_new_value(index: int, value: int, a: array<int>): int
    reads a
    ensures (index == 4) ==> (compute_new_value(index, value, a) == value + 3)
    ensures (index == 7) ==> (compute_new_value(index, value, a) == 516)
    ensures (index != 4 && index != 7) ==> (compute_new_value(index, value, a) == value)
{
    if index == 4 then 
        value + 3
    else if index == 7 then
        516
    else
        value
}
// </vc-helpers>

// <vc-spec>
method update_elements(a: array<int>) returns (result: array<int>)
    requires a.Length >= 8
    ensures result.Length == a.Length
    ensures result[4] == a[4] + 3
    ensures result[7] == 516
    ensures forall i :: 0 <= i < a.Length && i != 4 && i != 7 ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Initialize result array and populate it using compute_new_value */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> result[k] == compute_new_value(k, a[k], a)
  {
    result[i] := compute_new_value(i, a[i], a);
    i := i + 1;
  }
  return result;
}
// </vc-code>
