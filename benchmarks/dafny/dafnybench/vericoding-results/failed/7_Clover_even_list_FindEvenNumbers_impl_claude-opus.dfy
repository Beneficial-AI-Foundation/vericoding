

// <vc-helpers>
lemma EvenNumbersSubset(arr: array<int>, evenNumbers: array<int>, count: nat)
  requires count <= evenNumbers.Length
  requires forall i :: 0 <= i < count ==> evenNumbers[i] % 2 == 0
  requires forall i :: 0 <= i < count ==> exists j :: 0 <= j < arr.Length && evenNumbers[i] == arr[j]
  ensures forall x :: x in evenNumbers[..count] ==> x in arr[..]
{
  forall x | x in evenNumbers[..count]
    ensures x in arr[..]
  {
    var idx :| 0 <= idx < count && evenNumbers[idx] == x;
    var j :| 0 <= j < arr.Length && evenNumbers[idx] == arr[j];
    assert x == arr[j];
    assert x in arr[..];
  }
}

function CountEvens(arr: array<int>, n: nat): nat
  requires n <= arr.Length
  reads arr
{
  if n == 0 then 0
  else CountEvens(arr, n-1) + (if arr[n-1] % 2 == 0 then 1 else 0)
}

lemma CountEvensComplete(arr: array<int>)
  ensures CountEvens(arr, arr.Length) == |set i | 0 <= i < arr.Length && arr[i] % 2 == 0|
{
  var n := arr.Length;
  var s := set i | 0 <= i < n && arr[i] % 2 == 0;
  CountEvensIsCardinalityOfSet(arr, n, s);
}

lemma CountEvensIsCardinalityOfSet(arr: array<int>, n: nat, s: set<nat>)
  requires n <= arr.Length
  requires s == set i | 0 <= i < n && arr[i] % 2 == 0
  ensures CountEvens(arr, n) == |s|
{
  if n == 0 {
    assert s == {};
  } else {
    var s' := set i | 0 <= i < n-1 && arr[i] % 2 == 0;
    CountEvensIsCardinalityOfSet(arr, n-1, s');
    
    if arr[n-1] % 2 == 0 {
      assert s == s' + {n-1};
      assert n-1 !in s';
      assert |s| == |s'| + 1;
    } else {
      assert s == s';
    }
  }
}

predicate EvenAt(arr: array<int>, i: int)
  requires 0 <= i < arr.Length
  reads arr
{
  arr[i] % 2 == 0
}

function EvenIndices(arr: array<int>, n: nat): seq<nat>
  requires n <= arr.Length
  reads arr
  ensures forall i :: i in EvenIndices(arr, n) ==> 0 <= i < n && EvenAt(arr, i)
  ensures forall i :: 0 <= i < n && EvenAt(arr, i) ==> i in EvenIndices(arr, n)
  ensures |EvenIndices(arr, n)| == CountEvens(arr, n)
{
  if n == 0 then []
  else 
    var prev := EvenIndices(arr, n-1);
    if arr[n-1] % 2 == 0 then prev + [n-1] else prev
}

lemma AllEvensIncluded(arr: array<int>, evenNumbers: array<int>, indices: seq<nat>)
  requires forall m :: 0 <= m < |indices| ==> 0 <= indices[m] < arr.Length && arr[indices[m]] % 2 == 0
  requires forall m :: 0 <= m < |indices| ==> m < evenNumbers.Length && evenNumbers[m] == arr[indices[m]]
  requires forall m, n :: 0 <= m < n < |indices| ==> indices[m] < indices[n]
  requires |indices| == evenNumbers.Length
  requires forall i :: 0 <= i < arr.Length && arr[i] % 2 == 0 ==> exists m :: 0 <= m < |indices| && indices[m] == i
  ensures forall x :: x in arr[..] && x % 2 == 0 ==> x in evenNumbers[..]
{
  forall x | x in arr[..] && x % 2 == 0
    ensures x in evenNumbers[..]
  {
    var i :| 0 <= i < arr.Length && arr[i] == x;
    assert arr[i] % 2 == 0;
    var m :| 0 <= m < |indices| && indices[m] == i;
    assert evenNumbers[m] == arr[indices[m]] == arr[i] == x;
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
  // First pass: count even numbers
  var count := 0;
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant count == CountEvens(arr, i)
  {
    if arr[i] % 2 == 0 {
      count := count + 1;
    }
    i := i + 1;
  }
  
  assert count == CountEvens(arr, arr.Length);
  CountEvensComplete(arr);
  
  // Allocate result array
  evenNumbers := new int[count];
  
  if count == 0 {
    return;
  }
  
  // Second pass: copy even numbers  
  var j := 0;
  var k := 0;
  
  ghost var indices := [];
  
  while j < arr.Length
    invariant 0 <= j <= arr.Length
    invariant 0 <= k <= count
    invariant k <= CountEvens(arr, j)
    invariant count == CountEvens(arr, arr.Length)
    invariant |indices| == k
    invariant forall m :: 0 <= m < k ==> 0 <= indices[m] < j && arr[indices[m]] % 2 == 0
    invariant forall m :: 0 <= m < k ==> evenNumbers[m] == arr[indices[m]]
    invariant forall m, n :: 0 <= m < n < k ==> indices[m] < indices[n]
    invariant forall i :: 0 <= i < j && arr[i] % 2 == 0 ==> exists m :: 0 <= m < k && indices[m] == i
    invariant k == |set i | 0 <= i < j && arr[i] % 2 == 0|
  {
    if arr[j] % 2 == 0 {
      assert k < count;
      evenNumbers[k] := arr[j];
      indices := indices + [j];
      k := k + 1;
    }
    j := j + 1;
  }
  
  assert k == count;
  assert j == arr.Length;
  
  // Prove postconditions
  forall m | 0 <= m < evenNumbers.Length
    ensures evenNumbers[m] % 2 == 0
  {
    assert evenNumbers[m] == arr[indices[m]];
  }
  
  forall m, n | 0 <= m < n < evenNumbers.Length
    ensures exists p, q :: 0 <= p < q < arr.Length && evenNumbers[m] == arr[p] && evenNumbers[n] == arr[q]
  {
    assert evenNumbers[m] == arr[indices[m]] && evenNumbers[n] == arr[indices[n]];
    assert indices[m] < indices[n];
  }
  
  AllEvensIncluded(arr, evenNumbers, indices);
  EvenNumbersSubset(arr, evenNumbers, count);
}
// </vc-code>

