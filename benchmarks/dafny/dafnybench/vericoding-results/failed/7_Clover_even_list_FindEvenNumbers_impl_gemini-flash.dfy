

// <vc-helpers>
function IsEven(x: int): bool {
  x % 2 == 0
}

function calc_even_count(arr: array<int>, limit: int): int
  reads arr
  requires 0 <= limit <= arr.Length
  decreases limit
{
  if limit == 0 then
    0
  else
    (if IsEven(arr[limit-1]) then 1 else 0) + calc_even_count(arr, limit-1)
}
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
// </vc-spec>
// <vc-code>
{
  var count := 0;
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= count <= i
    invariant count == (calc_even_count(arr, i))
  {
    if IsEven(arr[i]) {
      count := count + 1;
    }
  }

  evenNumbers := new int[count];
  var evenIndex := 0;
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= evenIndex <= count
    invariant forall k :: 0 <= k < evenIndex ==> IsEven(evenNumbers[k])
    invariant forall k :: 0 <= k < evenIndex ==> evenNumbers[k] in arr[..]
    invariant forall k :: 0 <= k < evenIndex ==> exists m :: 0 <= m < i && evenNumbers[k] == arr[m] && IsEven(arr[m])
    invariant forall k :: 0 <= k < i && IsEven(arr[k]) ==> (exists l :: 0 <= l < evenIndex && evenNumbers[l] == arr[k])
  {
    if IsEven(arr[i]) {
      evenNumbers[evenIndex] := arr[i];
      evenIndex := evenIndex + 1;
    }
  }
}
// </vc-code>

