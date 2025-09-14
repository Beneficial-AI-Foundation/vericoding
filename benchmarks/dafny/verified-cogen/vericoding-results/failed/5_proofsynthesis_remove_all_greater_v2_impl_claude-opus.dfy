// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma body to be empty (bodyless lemma) */
function CountLessOrEqual(v: array<int>, e: int, i: int): nat
  requires 0 <= i <= v.Length
  reads v
{
  if i == 0 then 0
  else if v[i-1] <= e then CountLessOrEqual(v, e, i-1) + 1
  else CountLessOrEqual(v, e, i-1)
}

lemma CountLessOrEqualCorrect(v: array<int>, e: int, i: int)
  requires 0 <= i <= v.Length
  ensures CountLessOrEqual(v, e, i) <= i
  ensures forall k :: 0 <= k < i && v[k] <= e ==> CountLessOrEqual(v, e, k+1) > CountLessOrEqual(v, e, k)
{
  if i > 0 {
    CountLessOrEqualCorrect(v, e, i-1);
  }
}

predicate ArrayContains(arr: array<int>, val: int, upTo: int)
  requires 0 <= upTo <= arr.Length
  reads arr
{
  exists j :: 0 <= j < upTo && arr[j] == val
}

lemma ArrayContainsImpliesUnique(arr: array<int>, val: int, upTo: int, v: array<int>, i: int)
  requires 0 <= upTo <= arr.Length
  requires 0 <= i <= v.Length
  requires forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]
  requires forall k :: 0 <= k < upTo ==> exists j :: 0 <= j < i && v[j] == arr[k] && v[j] <= val
  requires forall k1, k2 :: 0 <= k1 < k2 < upTo ==> arr[k1] != arr[k2]
  ensures forall k :: 0 <= k < i && v[k] <= val ==> ArrayContains(arr, v[k], upTo) || v[k] == val
{
}
// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)
    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]
    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && (exists j :: 0 <= j < v.Length && v[j] == result[k])
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> (exists j :: 0 <= j < result.Length && result[j] == v[k])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added lemma call to prove idx < count */
{
  var count := 0;
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant count == CountLessOrEqual(v, e, i)
  {
    if v[i] <= e {
      count := count + 1;
    }
    i := i + 1;
  }
  
  result := new int[count];
  var idx := 0;
  i := 0;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant 0 <= idx <= count
    invariant idx == CountLessOrEqual(v, e, i)
    invariant count == CountLessOrEqual(v, e, v.Length)
    invariant forall k :: 0 <= k < idx ==> result[k] <= e
    invariant forall k :: 0 <= k < idx ==> exists j :: 0 <= j < i && v[j] == result[k] && v[j] <= e
    invariant forall k :: 0 <= k < i && v[k] <= e ==> exists j :: 0 <= j < idx && result[j] == v[k]
    invariant forall k1, k2 :: 0 <= k1 < k2 < idx ==> result[k1] != result[k2]
  {
    if v[i] <= e {
      CountLessOrEqualCorrect(v, e, v.Length);
      CountLessOrEqualCorrect(v, e, i+1);
      assert CountLessOrEqual(v, e, i+1) <= CountLessOrEqual(v, e, v.Length);
      result[idx] := v[i];
      idx := idx + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
