// <vc-preamble>
function pow2(n: nat): nat 
    decreases n
{
    if n == 0 then
        1
    else
        2 * pow2(n - 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method invert(bit_width: nat, a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        forall i :: 0 <= i < a.Length ==> result[i] == (pow2(bit_width) - 1) - a[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed variable type to int and loop range to prevent type and range errors. */
{
  result := new int[a.Length];
  var m: int := pow2(bit_width) - 1;
  for i: nat := 0 to a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == m - a[j]
    invariant result.Length == a.Length
  {
    result[i] := m - a[i];
  }
}
// </vc-code>
