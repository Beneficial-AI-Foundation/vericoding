predicate IsEven (n: int)
{
  n % 2 == 0
}

// <vc-helpers>
lemma FilterPreservesOrder<T>(arr: array<T>, pred: T -> bool, result: array<T>)
  requires forall i :: 0 <= i < result.Length ==> exists j :: 0 <= j < arr.Length && result[i] == arr[j] && pred(arr[j])
  requires forall i, j :: 0 <= i < j < result.Length ==> 
    exists n, m :: 0 <= n < m < arr.Length && result[i] == arr[n] && result[j] == arr[m]
  ensures forall k, l :: 0 <= k < l < result.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && result[k] == arr[n] && result[l] == arr[m]
{
}

method CountEvenNumbers(arr: array<int>) returns (count: nat)
  ensures count <= arr.Length
  ensures count == |set i | 0 <= i < arr.Length && IsEven(arr[i])|
{
  count := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant count == |set j | 0 <= j < i && IsEven(arr[j])|
    invariant count <= i
  {
    if IsEven(arr[i]) {
      SetCardinalityHelper(arr, i);
      count := count + 1;
    } else {
      SetCardinalityHelper(arr, i);
    }
    i := i + 1;
  }
}

lemma SetCardinalityHelper(arr: array<int>, i: int)
  requires 0 <= i < arr.Length
  ensures |set j | 0 <= j < i+1 && IsEven(arr[j])| <= |set j | 0 <= j < i && IsEven(arr[j])| + 1
  ensures IsEven(arr[i]) ==> |set j | 0 <= j < i+1 && IsEven(arr[j])| == |set j | 0 <= j < i && IsEven(arr[j])| + 1
  ensures !IsEven(arr[i]) ==> |set j | 0 <= j < i+1 && IsEven(arr[j])| == |set j | 0 <= j < i && IsEven(arr[j])|
{
  var S1 := set j | 0 <= j < i && IsEven(arr[j]);
  var S2 := set j | 0 <= j < i+1 && IsEven(arr[j]);
  
  if IsEven(arr[i]) {
    assert S2 == S1 + {i};
    assert i !in S1;
  } else {
    assert S2 == S1;
  }
}

lemma EvenCountCorrectness(arr: array<int>, evenNumbers: array<int>, evenCount: nat)
  requires evenCount == |set i | 0 <= i < arr.Length && IsEven(arr[i])|
  requires evenNumbers.Length == evenCount
  requires forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
{
  forall x | x !in arr[..]
    ensures x !in evenNumbers[..]
  {
    if x in evenNumbers[..] {
      assert false;
    }
  }
}

lemma OrderPreservationHelper(arr: array<int>, evenNumbers: array<int>, evenCount: nat)
  requires evenCount == |set i | 0 <= i < arr.Length && IsEven(arr[i])|
  requires evenNumbers.Length == evenCount
  requires forall j :: 0 <= j < evenNumbers.Length ==> exists k :: 0 <= k < arr.Length && evenNumbers[j] == arr[k] && IsEven(arr[k])
  requires forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m] && IsEven(arr[n]) && IsEven(arr[m])
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindEvenNumbers (arr: array<int>)
  returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..];
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
    ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var evenCount := CountEvenNumbers(arr);
  evenNumbers := new int[evenCount];
  
  if evenCount == 0 {
    return;
  }
  
  var evenIndex := 0;
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= evenIndex <= evenCount
    invariant evenIndex == |set j | 0 <= j < i && IsEven(arr[j])|
    invariant evenIndex <= evenNumbers.Length
    invariant forall j :: 0 <= j < evenIndex ==> IsEven(evenNumbers[j])
    invariant forall j :: 0 <= j < evenIndex ==> evenNumbers[j] in arr[..]
    invariant forall j :: 0 <= j < evenIndex ==> exists k :: 0 <= k < i && evenNumbers[j] == arr[k] && IsEven(arr[k])
    invariant forall x :: x in arr[0..i] && IsEven(x) ==> x in evenNumbers[0..evenIndex]
    invariant forall x :: x in evenNumbers[0..evenIndex] ==> x in arr[0..i] && IsEven(x)
    invariant forall k, l :: 0 <= k < l < evenIndex ==>
      exists n, m :: 0 <= n < m < i && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m] && IsEven(arr[n]) && IsEven(arr[m])
  {
    if IsEven(arr[i]) {
      SetCardinalityHelper(arr, i);
      assert evenIndex < evenCount;
      evenNumbers[evenIndex] := arr[i];
      evenIndex := evenIndex + 1;
    } else {
      SetCardinalityHelper(arr, i);
    }
    i := i + 1;
  }
  
  assert evenIndex == evenCount;
  assert evenNumbers.Length == evenCount;
  OrderPreservationHelper(arr, evenNumbers, evenCount);
}
// </vc-code>
