

// <vc-helpers>
lemma SeqContainsElements<T>(s: seq<T>, t: seq<T>)
  requires forall i :: 0 <= i < |t| ==> t[i] in s
  ensures forall x :: x in t ==> x in s
{
}

lemma ArraySliceContains<T>(arr: array<T>, i: int)
  requires 0 <= i < arr.Length
  ensures arr[i] in arr[..]
{
}

lemma SeqIndexPreservation<T>(s: seq<T>, indices: seq<int>)
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |s|
  requires forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]
  ensures forall i, j :: 0 <= i < j < |indices| ==>
    exists n, m :: 0 <= n < m < |s| && s[indices[i]] == s[n] && s[indices[j]] == s[m]
{
  forall i, j | 0 <= i < j < |indices|
    ensures exists n, m :: 0 <= n < m < |s| && s[indices[i]] == s[n] && s[indices[j]] == s[m]
  {
    var n := indices[i];
    var m := indices[j];
    assert 0 <= n < m < |s|;
    assert s[indices[i]] == s[n] && s[indices[j]] == s[m];
  }
}

lemma EvenNumbersOrderingProof(arr: array<int>, evenIndices: seq<int>, evenNumbers: array<int>)
  requires forall i :: 0 <= i < |evenIndices| ==> 0 <= evenIndices[i] < arr.Length
  requires forall i, j :: 0 <= i < j < |evenIndices| ==> evenIndices[i] < evenIndices[j]
  requires evenNumbers.Length == |evenIndices|
  requires forall k :: 0 <= k < evenNumbers.Length ==> 0 <= k < |evenIndices|
  requires forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] == arr[evenIndices[k]]
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
  forall k, l | 0 <= k < l < evenNumbers.Length
    ensures exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
  {
    assert 0 <= k < l < |evenIndices|;
    var n := evenIndices[k];
    var m := evenIndices[l];
    assert 0 <= n < m < arr.Length;
    assert evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m];
  }
}

lemma EvenIndicesContainment(arr: array<int>, evenIndices: seq<int>)
  requires forall i :: 0 <= i < |evenIndices| ==> 0 <= evenIndices[i] < arr.Length
  requires forall i :: 0 <= i < |evenIndices| ==> arr[evenIndices[i]] % 2 == 0
  requires forall j :: 0 <= j < arr.Length && arr[j] % 2 == 0 ==> j in evenIndices
  ensures forall x :: x in arr[..] && x % 2 == 0 ==> exists k :: 0 <= k < |evenIndices| && arr[evenIndices[k]] == x
{
  forall x | x in arr[..] && x % 2 == 0
    ensures exists k :: 0 <= k < |evenIndices| && arr[evenIndices[k]] == x
  {
    assert exists j :: 0 <= j < arr.Length && arr[j] == x;
    var j :| 0 <= j < arr.Length && arr[j] == x;
    assert j in evenIndices;
    assert exists k :: 0 <= k < |evenIndices| && evenIndices[k] == j;
    var k :| 0 <= k < |evenIndices| && evenIndices[k] == j;
    assert arr[evenIndices[k]] == x;
  }
}

lemma EvenNumbersNotInArray(arr: array<int>, evenNumbers: array<int>, evenIndices: seq<int>)
  requires evenNumbers.Length == |evenIndices|
  requires forall k :: 0 <= k < evenNumbers.Length ==> 0 <= k < |evenIndices|
  requires forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] == arr[evenIndices[k]]
  requires forall i :: 0 <= i < |evenIndices| ==> 0 <= evenIndices[i] < arr.Length
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
{
}

lemma IndexOrderPreservation(evenIndices: seq<int>)
  requires forall k, l :: 0 <= k < l < |evenIndices| ==> evenIndices[k] < evenIndices[l]
  ensures forall i, j :: 0 <= i < j < |evenIndices| ==> evenIndices[i] < evenIndices[j]
{
}

lemma EvenElementsInResult(arr: array<int>, evenNumbers: array<int>, evenIndices: seq<int>)
  requires evenNumbers.Length == |evenIndices|
  requires forall k :: 0 <= k < evenNumbers.Length ==> 0 <= k < |evenIndices|
  requires forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] == arr[evenIndices[k]]
  requires forall i :: 0 <= i < |evenIndices| ==> 0 <= evenIndices[i] < arr.Length
  requires forall i :: 0 <= i < |evenIndices| ==> arr[evenIndices[i]] % 2 == 0
  requires forall j :: 0 <= j < arr.Length && arr[j] % 2 == 0 ==> j in evenIndices
  ensures forall x :: x in arr[..] && x % 2 == 0 ==> x in evenNumbers[..]
{
  forall x | x in arr[..] && x % 2 == 0
    ensures x in evenNumbers[..]
  {
    assert exists j :: 0 <= j < arr.Length && arr[j] == x;
    var j :| 0 <= j < arr.Length && arr[j] == x;
    assert j in evenIndices;
    assert exists k :: 0 <= k < |evenIndices| && evenIndices[k] == j;
    var k :| 0 <= k < |evenIndices| && evenIndices[k] == j;
    assert evenNumbers[k] == arr[evenIndices[k]] == arr[j] == x;
    assert x in evenNumbers[..];
  }
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
  var evenIndices: seq<int> := [];
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < |evenIndices| ==> 0 <= evenIndices[k] < i
    invariant forall k :: 0 <= k < |evenIndices| ==> arr[evenIndices[k]] % 2 == 0
    invariant forall k, l :: 0 <= k < l < |evenIndices| ==> evenIndices[k] < evenIndices[l]
    invariant forall j :: 0 <= j < i && arr[j] % 2 == 0 ==> j in evenIndices
  {
    if arr[i] % 2 == 0 {
      evenIndices := evenIndices + [i];
    }
    i := i + 1;
  }
  
  evenNumbers := new int[|evenIndices|];
  
  i := 0;
  while i < |evenIndices|
    invariant 0 <= i <= |evenIndices|
    invariant evenNumbers.Length == |evenIndices|
    invariant forall k :: 0 <= k < i ==> evenNumbers[k] == arr[evenIndices[k]]
  {
    evenNumbers[i] := arr[evenIndices[i]];
    i := i + 1;
  }
  
  assert forall k :: 0 <= k < evenNumbers.Length ==> 0 <= k < |evenIndices|;
  assert forall i :: 0 <= i < |evenIndices| ==> 0 <= evenIndices[i] < arr.Length;
  assert forall j :: 0 <= j < arr.Length && arr[j] % 2 == 0 ==> j in evenIndices;
  
  IndexOrderPreservation(evenIndices);
  
  if evenNumbers.Length > 0 {
    EvenNumbersOrderingProof(arr, evenNumbers, evenIndices);
  }
  
  EvenElementsInResult(arr, evenNumbers, evenIndices);
  EvenNumbersNotInArray(arr, evenNumbers, evenIndices);
}
// </vc-code>

