// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function InArray(a: array<int>, val: int, n: int): bool
  requires 0 <= n <= a.Length
  reads a
{
  if n == 0 then false
  else if a[n-1] == val then true
  else InArray(a, val, n-1)
}

lemma InArrayPreserves(a: array<int>, val: int, n: int, i: int)
  requires 0 <= n <= a.Length
  requires 0 <= i < n
  ensures InArray(a, val, n) <==> InArray(a, val, n-1) || a[i] == val
{
  if n == 0 {
  } else if i == n-1 {
    if a[n-1] == val {
      assert InArray(a, val, n);
    } else {
      assert InArray(a, val, n) == InArray(a, val, n-1);
    }
  } else {
    InArrayPreserves(a, val, n-1, i);
  }
}

function CountInArray(a: array<int>, val: int, n: int): nat
  requires 0 <= n <= a.Length
  reads a
{
  if n == 0 then 0
  else if a[n-1] == val then 1 + CountInArray(a, val, n-1)
  else CountInArray(a, val, n-1)
}

lemma InArrayImpliesExists(a: array<int>, val: int, n: int)
  requires 0 <= n <= a.Length
  requires InArray(a, val, n)
  ensures exists k :: 0 <= k < n && a[k] == val
{
  if n == 0 {
  } else if a[n-1] == val {
  } else {
    InArrayImpliesExists(a, val, n-1);
  }
}

lemma UniqueArrayLemma(a: array<int>, n: nat)
  requires 0 <= n <= a.Length
  requires forall i, j :: 0 <= i < n && 0 <= j < i ==> a[i] != a[j]
  ensures forall k :: 0 <= k < n ==> InArray(a, a[k], n)
{
  if n > 0 {
    UniqueArrayLemma(a, n-1);
    assert InArray(a, a[n-1], n);
  }
}

lemma InArrayDefinitionLemma(a: array<int>, val: int, n: int)
  requires 0 <= n <= a.Length
  ensures InArray(a, val, n) ==> exists k :: 0 <= k < n && a[k] == val
{
  if n == 0 {
  } else {
    if a[n-1] == val {
    } else {
      InArrayDefinitionLemma(a, val, n-1);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method UniqueAll(arr: array<int>) returns (ret: array<int>)
    ensures
        ret.Length <= arr.Length &&
        (forall i :: 0 <= i < arr.Length ==> exists j :: 0 <= j < ret.Length && ret[j] == arr[i]) &&
        (forall i, j :: 0 <= i < ret.Length && 0 <= j < i ==> ret[i] != ret[j])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed loop invariants and verification */
  var unique := new int[arr.Length];
  var count := 0;
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= count <= i <= arr.Length
    invariant forall k :: 0 <= k < count ==> InArray(unique, unique[k], count)
    invariant forall k, j :: 0 <= k < count && 0 <= j < k ==> unique[k] != unique[j]
    invariant forall k :: 0 <= k < i ==> exists j :: 0 <= j < count && unique[j] == arr[k]
  {
    if !InArray(unique, arr[i], count) {
      unique[count] := arr[i];
      count := count + 1;
    }
    i := i + 1;
  }
  
  ret := new int[count];
  var j := 0;
  while j < count
    invariant 0 <= j <= count
    invariant forall k :: 0 <= k < j ==> ret[k] == unique[k]
    invariant forall k, l :: 0 <= k < j && 0 <= l < k ==> ret[k] != ret[l]
  {
    ret[j] := unique[j];
    j := j + 1;
  }
}
// </vc-code>
