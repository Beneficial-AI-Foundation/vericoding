predicate IsEven (n: int)
{
  n % 2 == 0
}

// <vc-helpers>
// Helper section: no additional helpers required for this implementation.
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
  var idxsArr := new int[arr.Length];
  var i := 0;
  var c := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= c <= i
    invariant forall t :: 0 <= t < i && IsEven(arr[t]) ==> (exists u :: 0 <= u < c && idxsArr[u] == t)
    invariant forall u :: 0 <= u < c ==> 0 <= idxsArr[u] < i && IsEven(arr[idxsArr[u]])
    invariant forall u, v :: 0 <= u < v < c ==> idxsArr[u] < idxsArr[v]
    invariant forall u :: 0 <= u < c ==> 0 <= idxsArr[u] < arr.Length
  {
    if IsEven(arr[i]) {
      idxsArr[c] := i;
      c := c + 1;
    }
    i := i + 1;
  }

  // i reached arr.Length, instantiate loop properties for full array
  assert i == arr.Length;
  assert forall t :: 0 <= t < arr.Length && IsEven(arr[t]) ==> (exists u :: 0 <= u < c && idxsArr[u] == t);
  assert forall u :: 0 <= u < c ==> 0 <= idxsArr[u] < arr.Length;
  assert forall u, v :: 0 <= u < v < c ==> idxsArr[u] < idxsArr[v];

  evenNumbers := new int[c];
  var k := 0;
  while k < c
    invariant 0 <= k <= c
    invariant forall u :: 0 <= u < k ==> evenNumbers[u] == arr[idxsArr[u]]
    invariant forall u :: 0 <= u < k ==> 0 <= idxsArr[u] < arr.Length
    invariant forall u, v :: 0 <= u < v < k ==> idxsArr[u] < idxsArr[v]
    invariant forall u :: 0 <= u < c ==> 0 <= idxsArr[u] < arr.Length
  {
    evenNumbers[k] := arr[idxsArr[k]];
    k := k + 1;
  }

  // k should equal c and evenNumbers filled accordingly
  assert k == c;
  assert forall u :: 0 <= u < c ==> evenNumbers[u] == arr[idxsArr[u]];

  // Prove postconditions

  // Any even element of arr is in evenNumbers
  assert forall t :: 0 <= t < arr.Length && IsEven(arr[t]) ==>
    (exists u :: 0 <= u < c && evenNumbers[u] == arr[t]);
  // This gives the required form for slice membership
  assert forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..];

  // Anything in evenNumbers comes from arr, so elements not in arr cannot be in evenNumbers
  assert forall u :: 0 <= u < evenNumbers.Length ==> evenNumbers[u] in arr[..];
  assert forall x :: x !in arr[..] ==> x !in evenNumbers[..];

  // Preserve original order: pick indices from idxsArr
  assert forall K, L :: 0 <= K < L < evenNumbers.Length ==>
    (exists n, m :: 0 <= n < m < arr.Length && evenNumbers[K] == arr[n] && evenNumbers[L] == arr[m]);
}
// </vc-code>

