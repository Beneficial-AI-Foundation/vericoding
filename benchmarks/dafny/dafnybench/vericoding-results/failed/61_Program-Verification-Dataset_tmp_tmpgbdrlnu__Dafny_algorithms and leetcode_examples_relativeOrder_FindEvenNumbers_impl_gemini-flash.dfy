predicate IsEven (n: int)
{
  n % 2 == 0
}

// <vc-helpers>
// No changes needed in helpers
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
    var count := 0;
    for i := 0 to arr.Length-1
        invariant 0 <= i <= arr.Length
        invariant 0 <= count <= i
        invariant forall k :: 0 <= k < i && IsEven(arr[k]) ==> (exists l :: 0 <= l < i && arr[l] == arr[k])
    {
        if IsEven(arr[i]) {
            count := count + 1;
        }
    }

    evenNumbers := new int[count];
    var j := 0;
    for i := 0 to arr.Length-1
        invariant 0 <= i <= arr.Length
        invariant 0 <= j <= count
        invariant (j == count) == (i == arr.Length || (if j < count then true else !exists k :: i <= k < arr.Length && IsEven(arr[k]))) // if j reaches count, then i must have scanned the entire array or no more even numbers exist
        invariant forall k :: 0 <= k < j ==> IsEven(evenNumbers[k]) && (exists l :: 0 <= l < i && evenNumbers[k] == arr[l])
        invariant forall k, l :: 0 <= k < l < j ==> (exists m, n :: 0 <= m < n < i && evenNumbers[k] == arr[m] && evenNumbers[l] == arr[n])
        invariant forall k :: 0 <= k < i && IsEven(arr[k]) ==> (exists l :: 0 <= l < j && evenNumbers[l] == arr[k]) || (exists tmp_k :: k <= tmp_k < i && arr[tmp_k] == arr[k] && IsEven(arr[tmp_k]))
    {
        if IsEven(arr[i]) {
            evenNumbers[j] := arr[i];
            j := j + 1;
        }
    }
}
// </vc-code>

