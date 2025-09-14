

// <vc-helpers>
predicate isEven(x: int) { x % 2 == 0 }

function filterEven(arr: seq<int>): seq<int>
{
  if |arr| == 0 then []
  else if isEven(arr[0]) then [arr[0]] + filterEven(arr[1..])
  else filterEven(arr[1..])
}

lemma filterEvenPreservesOrder(arr: seq<int>, k: nat, l: nat)
  requires 0 <= k < l < |filterEven(arr)|
  ensures exists n, m :: 0 <= n < m < |arr| && filterEven(arr)[k] == arr[n] && filterEven(arr)[l] == arr[m]
{
  if |arr| == 0 {
  } else if isEven(arr[0]) {
    var rest := filterEven(arr[1..]);
    if k == 0 && l > 0 {
      if l-1 < |rest| {
        filterEvenPreservesOrder(arr[1..], 0, l-1);
      }
    } else if k > 0 {
      filterEvenPreservesOrder(arr[1..], k-1, l-1);
    }
  } else {
    filterEvenPreservesOrder(arr[1..], k, l);
  }
}

lemma filterEvenContainsAllEven(arr: seq<int>)
  ensures forall x {:trigger (x%2)} :: x in arr && isEven(x) ==> x in filterEven(arr)
{
  if |arr| > 0 {
    if isEven(arr[0]) {
      filterEvenContainsAllEven(arr[1..]);
      forall x | x in arr && isEven(x) {
        if x == arr[0] {
        } else {
          assert x in arr[1..] && isEven(x);
          assert x in filterEven(arr[1..]);
        }
      }
    } else {
      filterEvenContainsAllEven(arr[1..]);
      forall x | x in arr && isEven(x) {
        assert x in arr[1..] && isEven(x);
        assert x in filterEven(arr[1..]);
      }
    }
  }
}

lemma filterEvenOnlyFromSource(arr: seq<int>)
  ensures forall x :: x in filterEven(arr) ==> x in arr
{
  if |arr| > 0 {
    filterEvenOnlyFromSource(arr[1..]);
    if isEven(arr[0]) {
      forall x | x in filterEven(arr) {
        if x == arr[0] {
        } else {
          assert x in filterEven(arr[1..]);
          assert x in arr[1..];
        }
      }
    } else {
      forall x | x in filterEven(arr) {
        assert x in filterEven(arr[1..]);
        assert x in arr[1..];
      }
    }
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
  var count := 0;
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant count == |filterEven(arr[0..i])|
  {
    if arr[i] % 2 == 0 {
      count := count + 1;
    }
    i := i + 1;
  }
  
  evenNumbers := new int[count];
  var j := 0;
  i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= j <= count
    invariant j == |filterEven(arr[0..i])|
    invariant forall k :: 0 <= k < j ==> evenNumbers[k] % 2 == 0
    invariant evenNumbers[0..j] == filterEven(arr[0..i])
    invariant forall k, l :: 0 <= k < l < j ==> exists n, m :: 0 <= n < m < i && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
  {
    if arr[i] % 2 == 0 {
      assert j < count;
      evenNumbers[j] := arr[i];
      j := j + 1;
      if j > 1 {
        filterEvenPreservesOrder(arr[0..i], j-2, j-1);
      }
    }
    i := i + 1;
  }
  filterEvenContainsAllEven(arr[..]);
  filterEvenOnlyFromSource(arr[..]);
}
// </vc-code>

