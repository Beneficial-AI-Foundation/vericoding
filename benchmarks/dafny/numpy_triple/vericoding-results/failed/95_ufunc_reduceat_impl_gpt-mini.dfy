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
/* helper modified by LLM (iteration 5): length property for ExtractSlice */
lemma SliceLengthProperty(arr: seq<real>, start: nat, end: nat)
  requires 0 <= start <= end <= |arr|
  ensures |ExtractSlice(arr, start, end)| == end - start
{
  assert |ExtractSlice(arr, start, end)| == end - start;
}

/* helper modified by LLM (iteration 5): elements of ExtractSlice correspond to arr entries and existence witness */
lemma SliceElementsWitness(arr: seq<real>, start: nat, end: nat)
  requires 0 <= start < end <= |arr|
  ensures exists elements: seq<real> :: elements == ExtractSlice(arr, start, end) && |elements| > 0 && (forall j :: 0 <= j < |elements| ==> exists k :: 0 <= k < |arr| && elements[j] == arr[k])
{
  var s := ExtractSlice(arr, start, end);
  SliceLengthProperty(arr, start, end);
  assert s == ExtractSlice(arr, start, end);
  assert |s| == end - start;
  assert end - start > 0;
  assert forall j :: 0 <= j < |s| ==> exists k :: 0 <= k < |arr| && s[j] == arr[k];
  assert exists elements: seq<real> :: elements == s && |elements| > 0 && (forall j :: 0 <= j < |elements| ==> exists k :: 0 <= k < |arr| && elements[j] == arr[k]);
}

/* helper modified by LLM (iteration 5): singleton witness for single-element sequence */
lemma SingletonWitness(arr: seq<real>, i: nat)
  requires i < |arr|
  ensures exists elements: seq<real> :: elements == [arr[i]] && |elements| > 0 && (forall j :: 0 <= j < |elements| ==> exists k :: 0 <= k < |arr| && elements[j] == arr[k])
{
  assert |[arr[i]]| == 1;
  assert [arr[i]][0] == arr[i];
  assert |[arr[i]]| > 0;
  assert forall j :: 0 <= j < |[arr[i]]| ==> exists k :: 0 <= k < |arr| && [arr[i]][j] == arr[k];
  assert exists elements: seq<real> :: elements == [arr[i]] && |elements| > 0 && (forall j :: 0 <= j < |elements| ==> exists k :: 0 <= k < |arr| && elements[j] == arr[k]);
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
/* code modified by LLM (iteration 5): construct result by folding slices with maintained invariants */
{
  var res: seq<real> := [];
  var n := |indices|;
  var aLen := |arr|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall k :: 0 <= k < |res| ==>
      if k < n - 1 then
        if indices[k] < indices[k+1] then
          |ExtractSlice(arr, indices[k], indices[k+1])| > 0 &&
          (forall j :: 0 <= j < |ExtractSlice(arr, indices[k], indices[k+1])| ==> exists l :: 0 <= l < aLen && ExtractSlice(arr, indices[k], indices[k+1])[j] == arr[l]) &&
          res[k] == LeftFold(op, ExtractSlice(arr, indices[k], indices[k+1]))
        else
          res[k] == LeftFold(op, ExtractSlice(arr, indices[k], indices[k]+1))
      else
        |ExtractSlice(arr, indices[k], aLen)| > 0 &&
        (forall j :: 0 <= j < |ExtractSlice(arr, indices[k], aLen)| ==> exists l :: 0 <= l < aLen && ExtractSlice(arr, indices[k], aLen)[j] == arr[l]) &&
        res[k] == LeftFold(op, ExtractSlice(arr, indices[k], aLen))
  {
    var start := indices[i];
    var e: real;
    if i < n - 1 {
      var next := indices[i+1];
      if start < next {
        var slice := ExtractSlice(arr, start, next);
        SliceElementsWitness(arr, start, next);
        assert |slice| > 0;
        e := LeftFold(op, slice);
      } else {
        var single := ExtractSlice(arr, start, start+1);
        SingletonWitness(arr, start);
        assert |single| > 0;
        e := LeftFold(op, single);
      }
    } else {
      var slice := ExtractSlice(arr, start, aLen);
      SliceElementsWitness(arr, start, aLen);
      assert |slice| > 0;
      e := LeftFold(op, slice);
    }
    res := res + [e];
    i := i + 1;
  }
  result := res;
}

// </vc-code>
