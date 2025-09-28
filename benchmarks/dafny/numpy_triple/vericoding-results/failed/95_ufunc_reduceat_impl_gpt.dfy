// <vc-preamble>
// Type alias for binary operation on reals
type BinaryOp = (real, real) -> real

// Helper predicate to check if all indices are valid for the given array length
predicate ValidIndices(indices: seq<nat>, arrayLen: nat)
{
    arrayLen > 0 && |indices| > 0 && forall i :: 0 <= i < |indices| ==> indices[i] < arrayLen
}

// Helper function to extract a slice from an array between two indices
function ExtractSlice(arr: seq<real>, start: nat, end: nat): seq<real>
    requires 0 <= start <= end <= |arr|
{
    arr[start..end]
}

// Helper function to perform left-associative fold on a non-empty sequence
function {:opaque} LeftFold(op: BinaryOp, elements: seq<real>): real
    requires |elements| > 0
{
    if |elements| == 1 then
        elements[0]
    else
        op(elements[0], LeftFold(op, elements[1..]))
}

// Main reduceat method specification
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Lemmas for LeftFold on singleton and slice properties (length, non-emptiness, element origin) */
lemma LeftFoldOfSingleton(op: BinaryOp, x: real)
  ensures LeftFold(op, [x]) == x
{
  reveal LeftFold();
}

/* helper modified by LLM (iteration 5): length of a slice is end - start */
lemma SliceLength(arr: seq<real>, s: nat, e: nat)
  requires s <= e <= |arr|
  ensures |ExtractSlice(arr, s, e)| == e - s
{
  assert ExtractSlice(arr, s, e) == arr[s..e];
  assert |arr[s..e]| == e - s;
}

/* helper modified by LLM (iteration 5): slice [s..e) is non-empty when s<e */
lemma SliceNonEmpty(arr: seq<real>, s: nat, e: nat)
  requires s < e <= |arr|
  ensures |ExtractSlice(arr, s, e)| > 0
{
  SliceLength(arr, s, e);
  assert |ExtractSlice(arr, s, e)| == e - s;
  assert e - s > 0;
}

/* helper modified by LLM (iteration 5): tail slice [s..|arr|) is non-empty when s<|arr| */
lemma SliceToEndNonEmpty(arr: seq<real>, s: nat)
  requires s < |arr|
  ensures |ExtractSlice(arr, s, |arr|)| > 0
{
  SliceLength(arr, s, |arr|);
  assert |ExtractSlice(arr, s, |arr|)| == |arr| - s;
  assert |arr| - s > 0;
}

/* helper modified by LLM (iteration 5): every element of a slice comes from the original array */
lemma SliceElementsComeFromArr(arr: seq<real>, s: nat, e: nat)
  requires s <= e <= |arr|
  ensures forall j :: 0 <= j < |ExtractSlice(arr, s, e)| ==> exists k :: 0 <= k < |arr| && ExtractSlice(arr, s, e)[j] == arr[k]
{
  SliceLength(arr, s, e);
  forall j | 0 <= j < |ExtractSlice(arr, s, e)|
    ensures exists k :: 0 <= k < |arr| && ExtractSlice(arr, s, e)[j] == arr[k]
  {
    assert |ExtractSlice(arr, s, e)| == e - s;
    assert j < e - s;
    var k := s + j;
    assert k < e;
    assert k < |arr|;
    assert k >= s;
    assert ExtractSlice(arr, s, e)[j] == arr[k];
  }
}

/* helper modified by LLM (iteration 5): singleton sequence element originates from the array */
lemma SingletonElementsComeFromArr(arr: seq<real>, idx: nat)
  requires idx < |arr|
  ensures forall j :: 0 <= j < |[arr[idx]]| ==> exists k :: 0 <= k < |arr| && [arr[idx]][j] == arr[k]
{
  forall j | 0 <= j < |[arr[idx]]|
    ensures exists k :: 0 <= k < |arr| && [arr[idx]][j] == arr[k]
  {
    assert j == 0;
    var k := idx;
    assert 0 <= k < |arr|;
    assert [arr[idx]][j] == arr[k];
  }
}
// </vc-helpers>

// <vc-spec>
method ReduceAt(op: BinaryOp, arr: seq<real>, indices: seq<nat>) returns (result: seq<real>)
    requires ValidIndices(indices, |arr|)
    ensures |result| == |indices|
    ensures forall i :: 0 <= i < |indices| ==> 
        // For non-last indices
        (i < |indices| - 1 ==> (
            var startIdx := indices[i];
            var endIdx := indices[i + 1];
            // Case 1: Normal forward slice (start < end)
            if startIdx < endIdx then
                var slice := ExtractSlice(arr, startIdx, endIdx);
                |slice| > 0 && result[i] == LeftFold(op, slice)
            // Case 2: Backward or equal indices (start >= end) 
            else
                result[i] == arr[startIdx]
        )) &&
        // For the last index: reduce from indices[i] to end of array
        (i == |indices| - 1 ==> (
            var startIdx := indices[i];
            var slice := ExtractSlice(arr, startIdx, |arr|);
            |slice| > 0 && result[i] == LeftFold(op, slice)
        ))
    ensures forall i :: 0 <= i < |indices| ==> 
        // All result elements are well-defined based on array contents
        exists elements: seq<real> :: 
            |elements| > 0 && 
            (forall j :: 0 <= j < |elements| ==> exists k :: 0 <= k < |arr| && elements[j] == arr[k]) &&
            result[i] == LeftFold(op, elements)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Implement ReduceAt with loop, ghost witnesses, and explicit proofs for postconditions */
  var n := |indices|;
  var res: seq<real> := [];
  ghost var elems: seq<seq<real>> := [];
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant |elems| == i
    invariant forall j :: 0 <= j < i ==>
      ((j < n - 1 ==>
        (var s := indices[j];
         var e := indices[j + 1];
         if s < e then
           var sl := ExtractSlice(arr, s, e);
           |sl| > 0 && res[j] == LeftFold(op, sl)
         else
           res[j] == arr[s]
        )) &&
       (j == n - 1 ==>
        (var s2 := indices[j];
         var sl2 := ExtractSlice(arr, s2, |arr|);
         |sl2| > 0 && res[j] == LeftFold(op, sl2)
        )))
    invariant forall j :: 0 <= j < i ==> res[j] == LeftFold(op, elems[j])
    invariant forall j :: 0 <= j < i ==> |elems[j]| > 0
    invariant forall j :: 0 <= j < i ==>
      (forall t :: 0 <= t < |elems[j]| ==> exists k :: 0 <= k < |arr| && elems[j][t] == arr[k])
    decreases n - i
  {
    var s := indices[i];
    if i < n - 1 {
      var e := indices[i + 1];
      if s < e {
        var sl := ExtractSlice(arr, s, e);
        SliceNonEmpty(arr, s, e);
        res := res + [LeftFold(op, sl)];
        elems := elems + [sl];
        SliceElementsComeFromArr(arr, s, e);
      } else {
        var v := arr[s];
        res := res + [v];
        elems := elems + [[v]];
        LeftFoldOfSingleton(op, v);
        SingletonElementsComeFromArr(arr, s);
      }
    } else {
      var sl2 := ExtractSlice(arr, s, |arr|);
      SliceToEndNonEmpty(arr, s);
      res := res + [LeftFold(op, sl2)];
      elems := elems + [sl2];
      SliceElementsComeFromArr(arr, s, |arr|);
    }
    i := i + 1;
  }
  assert i == n;

  // Prove existence-based postcondition explicitly using witnesses
  assert forall j :: 0 <= j < n ==> 
    exists elements: seq<real> ::
      |elements| > 0 &&
      (forall t :: 0 <= t < |elements| ==> exists k :: 0 <= k < |arr| && elements[t] == arr[k]) &&
      res[j] == LeftFold(op, elements)
  {
    var s := indices[j];
    if j < n - 1 {
      var e := indices[j + 1];
      if s < e {
        var sl := ExtractSlice(arr, s, e);
        SliceNonEmpty(arr, s, e);
        SliceElementsComeFromArr(arr, s, e);
        assert res[j] == LeftFold(op, sl);
        assert exists elements: seq<real> ::
          |elements| > 0 &&
          (forall t :: 0 <= t < |elements| ==> exists k :: 0 <= k < |arr| && elements[t] == arr[k]) &&
          res[j] == LeftFold(op, elements)
        by {
          var elements := sl;
          assert |elements| > 0;
          assert (forall t :: 0 <= t < |elements| ==> exists k :: 0 <= k < |arr| && elements[t] == arr[k]);
          assert res[j] == LeftFold(op, elements);
        }
      } else {
        var v := arr[s];
        assert res[j] == v;
        LeftFoldOfSingleton(op, v);
        SingletonElementsComeFromArr(arr, s);
        assert exists elements: seq<real> ::
          |elements| > 0 &&
          (forall t :: 0 <= t < |elements| ==> exists k :: 0 <= k < |arr| && elements[t] == arr[k]) &&
          res[j] == LeftFold(op, elements)
        by {
          var elements := [v];
          assert |elements| > 0;
          assert (forall t :: 0 <= t < |elements| ==> exists k :: 0 <= k < |arr| && elements[t] == arr[k]);
          assert LeftFold(op, elements) == v;
          assert res[j] == LeftFold(op, elements);
        }
      }
    } else {
      var sl2 := ExtractSlice(arr, s, |arr|);
      SliceToEndNonEmpty(arr, s);
      SliceElementsComeFromArr(arr, s, |arr|);
      assert res[j] == LeftFold(op, sl2);
      assert exists elements: seq<real> ::
        |elements| > 0 &&
        (forall t :: 0 <= t < |elements| ==> exists k :: 0 <= k < |arr| && elements[t] == arr[k]) &&
        res[j] == LeftFold(op, elements)
      by {
        var elements := sl2;
        assert |elements| > 0;
        assert (forall t :: 0 <= t < |elements| ==> exists k :: 0 <= k < |arr| && elements[t] == arr[k]);
        assert res[j] == LeftFold(op, elements);
      }
    }
  }

  result := res;
}
// </vc-code>
