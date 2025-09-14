// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed (==) constraints to avoid warnings and kept proofs constructive */
lemma MemberAppendRight<T>(s: seq<T>, x: T)
  ensures x in s + [x]
{
  assert |s + [x]| == |s| + 1;
  assert (s + [x])[|s|] == x;
  assert exists i: int :: i == |s| && 0 <= i < |s + [x]| && (s + [x])[i] == x;
}
/* helper modified by LLM (iteration 3): removed (==) constraints to avoid warnings */
lemma MemberMonotoneConcat<T>(s: seq<T>, t: seq<T>, x: T)
  ensures x in s ==> x in s + t
{
  if x in s {
    var i: int :| 0 <= i < |s| && s[i] == x;
    assert 0 <= i < |s + t|;
    assert (s + t)[i] == x;
  }
}
/* helper modified by LLM (iteration 3): removed (==) constraints to avoid warnings */
lemma IndexInArraySlice<T>(a: array<T>, i: int)
  requires 0 <= i < a.Length
  ensures a[i] in a[..]
{
  assert |a[..]| == a.Length;
  assert a[..][i] == a[i];
  assert exists j: int :: j == i && 0 <= j < |a[..]| && a[..][j] == a[i];
}
// </vc-helpers>

// <vc-spec>
method RemoveElements(arr1: array<int>, arr2: array<int>) returns (result: seq<int>)
    ensures
        forall i: int ::
            0 <= i < |result| ==> (result[i] in arr1[..] && !(result[i] in arr2[..]))
    ensures
        forall i: int ::
            0 <= i < arr1.Length ==> (arr1[i] in arr2[..] || arr1[i] in result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): filtering with quantified invariants; record pre-update coverage in rold */
  var r: seq<int> := [];
  var i: int := 0;
  while i < arr1.Length
    invariant 0 <= i <= arr1.Length
    invariant forall j: int :: 0 <= j < |r| ==> (r[j] in arr1[..] && !(r[j] in arr2[..]))
    invariant forall k: int :: 0 <= k < i ==> (arr1[k] in arr2[..] || arr1[k] in r)
  {
    var x := arr1[i];
    if !(x in arr2[..]) {
      // capture current r and the coverage property for indices < i
      var rold := r;
      assert forall k0: int :: 0 <= k0 < i ==> (arr1[k0] in arr2[..] || arr1[k0] in rold);
      // append x, which is from arr1 and not in arr2
      IndexInArraySlice(arr1, i);
      r := rold + [x];
      assert r[|rold|] == x;
      assert x in arr1[..];
      assert r[|rold|] in arr1[..];
      assert !(r[|rold|] in arr2[..]);
      // maintain second invariant for prior elements
      forall k | 0 <= k < i
        ensures arr1[k] in arr2[..] || arr1[k] in r
      {
        if !(arr1[k] in arr2[..]) {
          // by the assertion above, arr1[k] is in rold, hence in r = rold + [x]
          MemberMonotoneConcat(rold, [x], arr1[k]);
        }
      }
    }
    i := i + 1;
  }
  result := r;
}
// </vc-code>
