// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Converted to recursive function to avoid loop in function body */
function CountEvensInPrefix(arr: array<int>, prefix: int): int
  requires 0 <= prefix <= arr.Length
  ensures CountEvensInPrefix(arr, prefix) == |set j | 0 <= j < prefix && IsEven(arr[j])|
{
  if prefix == 0 then 0
  else if IsEven(arr[prefix-1]) then 1 + CountEvensInPrefix(arr, prefix-1)
  else CountEvensInPrefix(arr, prefix-1)
}
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (result: array<int>)
    ensures forall x :: x in result[..] ==> IsEven(x) && x in arr[..]
    ensures forall x :: x in arr[..] && IsEven(x) ==> x in result[..]
    ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i <= j 
        && IsEven(arr[i]) && IsEven(arr[j]) ==> 
        exists ri, rj :: 0 <= ri < result.Length && 0 <= rj < result.Length 
            && ri <= rj && result[ri] == arr[i] && result[rj] == arr[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced count logic with recursive helper and strengthened invariants for order preservation */
{
  var numEvens := CountEvensInPrefix(arr, arr.Length);
  result := new int[numEvens];
  var idx := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= idx <= numEvens
    invariant idx == CountEvensInPrefix(arr, i)
    invariant forall k :: 0 <= k < idx ==> result[k] == arr[j] where CountEvensInPrefix(arr, i) gives the mapping
  {
    if IsEven(arr[i])
    {
      result[idx] := arr[i];
      idx := idx + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
