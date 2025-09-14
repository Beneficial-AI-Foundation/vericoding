// <vc-preamble>
predicate IsEven (n: int)
{
  n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes from iteration 4 */
function CountEvens(arr: array<int>, limit: int): nat
  requires 0 <= limit <= arr.Length
{
  |set i: int | 0 <= i < limit && IsEven(arr[i])|
}
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers (arr: array<int>)
  returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..];
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
    ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed compilation error by using a ghost block for ghost variable assignment */
  var count := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant count == CountEvens(arr, i)
  {
    if IsEven(arr[i]) {
      count := count + 1;
    }
    i := i + 1;
  }

  evenNumbers := new int[count];
  ghost var original_indices := new int[count];

  var k := 0;
  var j := 0;
  while j < arr.Length
    invariant 0 <= j <= arr.Length
    invariant 0 <= k <= count
    invariant k == CountEvens(arr, j)
    invariant forall l :: 0 <= l < k ==> IsEven(evenNumbers[l])
    invariant forall l :: 0 <= l < k ==> evenNumbers[l] == arr[original_indices[l]]
    invariant forall l :: 0 <= l < k ==> 0 <= original_indices[l] < j
    invariant forall p, q :: 0 <= p < q < k ==> original_indices[p] < original_indices[q]
  {
    if IsEven(arr[j]) {
      evenNumbers[k] := arr[j];
      ghost { original_indices[k] := j; }
      k := k + 1;
    }
    j := j + 1;
  }
}
// </vc-code>
