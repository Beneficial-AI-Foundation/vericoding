// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>

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
  var count := 0;
  for i := 0 to arr.Length - 1
    if IsEven(arr[i])
      count := count + 1;
  result := new int[count];
  var idx := 0;
  for i := 0 to arr.Length - 1
    if IsEven(arr[i]) {
      result[idx] := arr[i];
      idx := idx + 1;
    }
}
// </vc-code>
