predicate IsEven (n: int)
{
  n % 2 == 0
}

// <vc-helpers>
lemma SeqContainsEquivalence<T>(s: seq<T>, x: T)
  ensures (x in s) <==> (exists i :: 0 <= i < |s| && s[i] == x)
{
}

lemma ArrayToSeqContains<T>(arr: array<T>, x: T)
  ensures (x in arr[..]) <==> (exists i :: 0 <= i < arr.Length && arr[i] == x)
{
  SeqContainsEquivalence(arr[..], x);
}

lemma PreserveOrder(arr: array<int>, evenIndices: seq<int>, evenNumbers: array<int>)
  requires |evenIndices| == evenNumbers.Length
  requires forall i :: 0 <= i < |evenIndices| ==> 0 <= evenIndices[i] < arr.Length
  requires forall i :: 0 <= i < |evenIndices| ==> IsEven(arr[evenIndices[i]])
  requires forall i :: 0 <= i < evenNumbers.Length ==> evenNumbers[i] == arr[evenIndices[i]]
  requires forall i, j :: 0 <= i < j < |evenIndices| ==> evenIndices[i] < evenIndices[j]
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
  forall k, l | 0 <= k < l < evenNumbers.Length
    ensures exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
  {
    var n := evenIndices[k];
    var m := evenIndices[l];
    assert evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m];
    assert n < m;
  }
}

lemma EmptyOrderPreservation(evenNumbers: array<int>)
  requires evenNumbers.Length == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < 0 && evenNumbers[k] == 0 && evenNumbers[l] == 0
{
  // Vacuously true since no k, l exist
}

lemma EvenIndicesInvariantPreservation(arr: array<int>, evenIndices: seq<int>, i: int)
  requires 0 <= i < arr.Length
  requires forall j, k :: 0 <= j < k < |evenIndices| ==> evenIndices[j] < evenIndices[k]
  requires forall j :: 0 <= j < |evenIndices| ==> evenIndices[j] < i
  requires IsEven(arr[i])
  ensures forall j, k :: 0 <= j < k < |evenIndices + [i]| ==> (evenIndices + [i])[j] < (evenIndices + [i])[k]
{
  var newEvenIndices := evenIndices + [i];
  forall j, k | 0 <= j < k < |newEvenIndices|
    ensures newEvenIndices[j] < newEvenIndices[k]
  {
    if k == |newEvenIndices| - 1 {
      assert newEvenIndices[k] == i;
      assert j < |evenIndices|;
      assert newEvenIndices[j] == evenIndices[j];
      assert evenIndices[j] < i;
    } else {
      assert j < k < |evenIndices|;
      assert newEvenIndices[j] == evenIndices[j];
      assert newEvenIndices[k] == evenIndices[k];
    }
  }
}

lemma EvenElementsInvariantPreservation(arr: array<int>, evenIndices: seq<int>, i: int)
  requires 0 <= i < arr.Length
  requires forall x :: x in arr[0..i] && IsEven(x) ==> exists j :: 0 <= j < |evenIndices| && 0 <= evenIndices[j] < arr.Length && arr[evenIndices[j]] == x
  requires forall j :: 0 <= j < |evenIndices| ==> 0 <= evenIndices[j] < arr.Length
  requires forall j :: 0 <= j < |evenIndices| ==> IsEven(arr[evenIndices[j]])
  requires forall j :: 0 <= j < |evenIndices| ==> evenIndices[j] < i
  requires IsEven(arr[i])
  ensures forall x :: x in arr[0..i+1] && IsEven(x) ==> exists j :: 0 <= j < |evenIndices + [i]| && 0 <= (evenIndices + [i])[j] < arr.Length && arr[(evenIndices + [i])[j]] == x
{
  var newEvenIndices := evenIndices + [i];
  forall x | x in arr[0..i+1] && IsEven(x)
    ensures exists j :: 0 <= j < |newEvenIndices| && 0 <= newEvenIndices[j] < arr.Length && arr[newEvenIndices[j]] == x
  {
    if x == arr[i] {
      assert arr[newEvenIndices[|newEvenIndices|-1]] == x;
    } else {
      assert x in arr[0..i];
      var j :| 0 <= j < |evenIndices| && 0 <= evenIndices[j] < arr.Length && arr[evenIndices[j]] == x;
      assert arr[newEvenIndices[j]] == x;
    }
  }
}

lemma AllEvensFound(arr: array<int>, evenIndices: seq<int>)
  requires forall j :: 0 <= j < |evenIndices| ==> 0 <= evenIndices[j] < arr.Length
  requires forall j :: 0 <= j < |evenIndices| ==> IsEven(arr[evenIndices[j]])
  requires forall x :: x in arr[0..arr.Length] && IsEven(x) ==> exists j :: 0 <= j < |evenIndices| && 0 <= evenIndices[j] < arr.Length && arr[evenIndices[j]] == x
  ensures forall x :: x in arr[..] && IsEven(x) ==> exists j :: 0 <= j < |evenIndices| && 0 <= evenIndices[j] < arr.Length && arr[evenIndices[j]] == x
{
  assert arr[0..arr.Length] == arr[..];
}

lemma FinalPostconditions(arr: array<int>, evenIndices: seq<int>, evenNumbers: array<int>)
  requires |evenIndices| == evenNumbers.Length
  requires forall j :: 0 <= j < |evenIndices| ==> 0 <= evenIndices[j] < arr.Length
  requires forall j :: 0 <= j < |evenIndices| ==> IsEven(arr[evenIndices[j]])
  requires forall x :: x in arr[..] && IsEven(x) ==> exists j :: 0 <= j < |evenIndices| && 0 <= evenIndices[j] < arr.Length && arr[evenIndices[j]] == x
  requires forall i :: 0 <= i < evenNumbers.Length ==> evenNumbers[i] == arr[evenIndices[i]]
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
{
  forall x | x in arr[..] && IsEven(x)
    ensures x in evenNumbers[..]
  {
    var j :| 0 <= j < |evenIndices| && 0 <= evenIndices[j] < arr.Length && arr[evenIndices[j]] == x;
    assert evenNumbers[j] == x;
    assert x in evenNumbers[..];
  }

  forall x | x !in arr[..]
    ensures x !in evenNumbers[..]
  {
    if x in evenNumbers[..] {
      var j :| 0 <= j < evenNumbers.Length && evenNumbers[j] == x;
      assert evenNumbers[j] == arr[evenIndices[j]];
      assert x == arr[evenIndices[j]];
      assert x in arr[..];
      assert false;
    }
  }
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
  var evenIndices: seq<int> := [];
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < |evenIndices| ==> 0 <= evenIndices[j] < arr.Length
    invariant forall j :: 0 <= j < |evenIndices| ==> IsEven(arr[evenIndices[j]])
    invariant forall j, k :: 0 <= j < k < |evenIndices| ==> evenIndices[j] < evenIndices[k]
    invariant forall x :: x in arr[0..i] && IsEven(x) ==> exists j :: 0 <= j < |evenIndices| && 0 <= evenIndices[j] < arr.Length && arr[evenIndices[j]] == x
    invariant forall j :: 0 <= j < |evenIndices| ==> evenIndices[j] < i
  {
    if IsEven(arr[i]) {
      EvenIndicesInvariantPreservation(arr, evenIndices, i);
      EvenElementsInvariantPreservation(arr, evenIndices, i);
      evenIndices := evenIndices + [i];
    }
    i := i + 1;
  }
  
  AllEvensFound(arr, evenIndices);
  
  evenNumbers := new int[|evenIndices|];
  i := 0;
  
  while i < |evenIndices|
    invariant 0 <= i <= |evenIndices|
    invariant forall j :: 0 <= j < i ==> evenNumbers[j] == arr[evenIndices[j]]
  {
    evenNumbers[i] := arr[evenIndices[i]];
    i := i + 1;
  }
  
  if evenNumbers.Length > 0 {
    PreserveOrder(arr, evenIndices, evenNumbers);
  }
  FinalPostconditions(arr, evenIndices, evenNumbers);
}
// </vc-code>

