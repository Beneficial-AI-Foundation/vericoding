// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
function FilterEven(arr: array<int>) returns (evenArr: array<int>)
  ensures forall x :: x in evenArr[..] ==> IsEven(x) && x in arr[..]
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenArr[..]
  ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i <= j 
      && IsEven(arr[i]) && IsEven(arr[j]) ==> 
      exists ri, rj :: 0 <= ri < evenArr.Length && 0 <= rj < evenArr.Length 
          && ri <= rj && evenArr[ri] == arr[i] && evenArr[rj] == arr[j]
{
  var count := 0;
  var index := 0;
  
  while index < arr.Length
    invariant 0 <= count <= index <= arr.Length
    invariant forall k :: 0 <= k < index && IsEven(arr[k]) ==> count > 0
    invariant forall x :: x in arr[0..index] && IsEven(x) ==> x in arr[0..index]
  {
    if IsEven(arr[index]) {
      count := count + 1;
    }
    index := index + 1;
  }
  
  result := new int[count];
  var resultIndex := 0;
  index := 0;
  
  while index < arr.Length
    invariant 0 <= resultIndex <= count
    invariant index <= arr.Length
    invariant forall k :: 0 <= k < index && IsEven(arr[k]) ==> resultIndex > 0
    invariant forall x :: x in result[0..resultIndex] ==> IsEven(x) && x in arr[0..index]
    invariant forall x :: x in arr[0..index] && IsEven(x) ==> x in result[0..resultIndex]
    invariant forall i, j :: 0 <= i < index && 0 <= j < index && i <= j 
        && IsEven(arr[i]) && IsEven(arr[j]) ==> 
        exists ri, rj :: 0 <= ri < resultIndex && 0 <= rj < resultIndex 
            && ri <= rj && result[ri] == arr[i] && result[rj] == arr[j]
  {
    if IsEven(arr[index]) {
      result[resultIndex] := arr[index];
      resultIndex := resultIndex + 1;
    }
    index := index + 1;
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
  result := FilterEven(arr);
}
// </vc-code>
