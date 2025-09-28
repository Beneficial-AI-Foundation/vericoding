// <vc-preamble>
function MultisetCount<T(==)>(s: seq<T>, x: T): nat
{
    |set i | 0 <= i < |s| && s[i] == x|
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Sort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]) &&
        (forall x :: MultisetCount(result[..], x) == MultisetCount(a[..], x))
// </vc-spec>
// <vc-code>
{
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
  {
    result[i] := a[i];
    i := i + 1;
  }
  
  if result.Length == 0 {
    return;
  }
  
  i := 1;
  while i < result.Length
    invariant 1 <= i <= result.Length
    invariant forall j, k :: 0 <= j < k < i ==> result[j] <= result[k]
    invariant multiset(result[..]) == multiset(a[..])
  {
    var key := result[i];
    var j := i - 1;
    
    while j >= 0 && result[j] > key
      invariant -1 <= j < i
      invariant forall k :: j < k < i ==> result[k] > key
      invariant forall k :: i < k < result.Length ==> result[k] == old(result[k])
      invariant forall k :: 0 <= k <= j ==> result[k] == old(result[k])
      invariant multiset(result[..]) + multiset{key} == multiset(old(result[..]))
      invariant forall p, q :: 0 <= p < q <= j ==> result[p] <= result[q]
      invariant forall p, q :: j + 1 < p < q < i ==> result[p] <= result[q]
      invariant forall p :: j + 1 < p < i ==> result[p] == old(result[p + 1])
    {
      result[j + 1] := result[j];
      j := j - 1;
    }
    
    result[j + 1] := key;
    i := i + 1;
  }
}
// </vc-code>
