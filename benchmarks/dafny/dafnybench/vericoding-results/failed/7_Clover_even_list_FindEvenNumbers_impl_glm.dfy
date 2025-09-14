

// <vc-helpers>
predicate appearsBefore(a: array<int>, x: int, n: int, y: int, m: int)
  reads a
  requires 0 <= n < a.Length && 0 <= m < a.Length
{
  a[n] == x && a[m] == y && n < m
}

predicate preservesOrder(a: array<int>, b: array<int>)
  reads a, b
  ensures preservesOrder(a, b) ==> forall k :: 0 <= k < b.Length ==> b[k] in a[..]
{
  forall k, l :: 0 <= k < l < b.Length ==>
    exists n, m :: 0 <= n < m < a.Length && appearsBefore(a, b[k], n, b[l], m)
}

lemma array_order_preservation(arr: array<int>, evenNumbers: array<int>)
  requires forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  requires forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  requires forall x {:trigger (x%2)} :: x in arr[..] && (x%2==0) ==> x in evenNumbers[..]
  ensures preservesOrder(arr, evenNumbers)
{
  forall k, l | 0 <= k < l < evenNumbers.Length
    ensures exists n, m :: 0 <= n < m < arr.Length && arr[n] == evenNumbers[k] && arr[m] == evenNumbers[l]
  {
    var nk:=-1;
    var ml:=-1;
    var firstFound := false;
    var secondFound := false;
    for i:=0 to arr.Length
      invariant 0 <= i <= arr.Length
      invariant nk == -1 ==> !firstFound
      invariant ml == -1 ==> !secondFound
      invariant firstFound ==> nk >= 0 && nk < i && arr[nk] == evenNumbers[k]
      invariant secondFound ==> ml >= 0 && ml < i && arr[ml] == evenNumbers[l] && nk < ml
    {
      if i < arr.Length {
        if !firstFound && arr[i] == evenNumbers[k] {
          nk := i;
          firstFound := true;
        }
        if firstFound && !secondFound && arr[i] == evenNumbers[l] && i > nk {
          ml := i;
          secondFound := true;
        }
      }
    }
    assert firstFound;
    assert secondFound;
    assert nk >= 0;
    assert ml >= 0;
    assert nk < ml;
    assert arr[nk] == evenNumbers[k];
    assert arr[ml] == evenNumbers[l];
    assert 0 <= nk < arr.Length;
    assert 0 <= ml < arr.Length;
  }
}

function CountEven(s: seq<int>): nat
  decreases s
{
  if |s| == 0 then 0
  else (if s[0] % 2 == 0 then 1 else 0) + CountEven(s[1..])
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
  for i:=0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant count == CountEven(arr[0..i])
  {
    if i < arr.Length && arr[i] % 2 == 0 {
      count := count + 1;
    }
  }
  evenNumbers := new int[count];
  var j := 0;
  for i:=0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= j <= count
    invariant j == CountEven(arr[0..i])
    invariant forall k :: 0 <= k < j ==> evenNumbers[k] in arr[0..i] && evenNumbers[k] % 2 == 0
    invariant forall x :: x in arr[0..i] && x % 2 == 0 ==> x in evenNumbers[0..j]
  {
    if i < arr.Length && arr[i] % 2 == 0 {
      evenNumbers[j] := arr[i];
      j := j + 1;
    }
  }
  array_order_preservation(arr, evenNumbers);
}
// </vc-code>

