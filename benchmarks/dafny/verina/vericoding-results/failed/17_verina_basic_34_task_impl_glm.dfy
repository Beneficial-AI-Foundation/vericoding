// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed for loop variable type declaration */
function CountEvenNumbers(arr: array<int>): int {
  var count := 0;
  for i: int := 0 to arr.Length
  {
    if IsEven(arr[i]) {
      count := count + 1;
    }
  }
  return count;
}

/* helper modified by LLM (iteration 3): fixed for loop variable type declaration */
method CopyEvenNumbers(arr: array<int>, result: array<int>) {
  var index := 0;
  for i: int := 0 to arr.Length
  {
    if IsEven(arr[i]) {
      result[index] := arr[i];
      index := index + 1;
    }
  }
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
{
  /* code modified by LLM (iteration 3): fixed helper function compilation issues */
  var count := CountEvenNumbers(arr);
  result := new int[count];
  CopyEvenNumbers(arr, result);
}
// </vc-code>
