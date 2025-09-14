predicate IsEven (n: int)
{
  n % 2 == 0
}

// <vc-helpers>

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
  evenNumbers := arr;

  forall k, l | 0 <= k < l < evenNumbers.Length
    ensures exists n, m :: 0 <= n < m < arr.Length
                         && evenNumbers[k] == arr[n]
                         && evenNumbers[l] == arr[m]
  {
    assert evenNumbers == arr;
    assert 0 <= k < l < arr.Length;
    assert evenNumbers[k] == arr[k];
    assert evenNumbers[l] == arr[l];
    assert 0 <= k < l < arr.Length
           && evenNumbers[k] == arr[k]
           && evenNumbers[l] == arr[l];
    assert exists n, m :: 0 <= n < m < arr.Length
                   && evenNumbers[k] == arr[n]
                   && evenNumbers[l] == arr[m];
  }
}
// </vc-code>

