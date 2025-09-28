// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [relate membership to index existence] */
lemma SeqElemIndex(s: seq<int>, v:int)
  decreases |s|
  ensures v in s <==> exists i :: 0 <= i < |s| && s[i] == v
{
  if |s| == 0 {
  } else {
    if s[0] == v {
    } else {
      SeqElemIndex(s[1..], v);
    }
  }
}

/* helper modified by LLM (iteration 5): [connect loop invariant to final postcondition] */
lemma InvariantToPost(ar1: seq<int>, ar2: seq<int>, res: seq<int>, i: int)
  requires 0 <= i <= |ar1|
  requires forall k :: 0 <= k < |res| ==> (exists j :: 0 <= j < i && ar1[j] == res[k])
  requires forall k :: 0 <= k < |res| ==> forall l :: 0 <= l < |ar2| ==> res[k] != ar2[l]
  ensures forall k :: 0 <= k < |res| ==> (exists j :: 0 <= j < |ar1| && ar1[j] == res[k]) && (forall l :: 0 <= l < |ar2| ==> res[k] != ar2[l])
{
  // trivial from requires and i <= |ar1|
}

// </vc-helpers>

// <vc-spec>
method setdiff1d(ar1: seq<int>, ar2: seq<int>) returns (result: seq<int>)
    // Each element in result is from ar1 and not in ar2
    ensures forall i :: 0 <= i < |result| ==> 
        (exists j :: 0 <= j < |ar1| && result[i] == ar1[j]) &&
        (forall k :: 0 <= k < |ar2| ==> result[i] != ar2[k])
    
    // No duplicates in result
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    
    // Result is sorted in ascending order
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    
    // All unique values from ar1 not in ar2 are included in result
    ensures forall val {:trigger val in ar1} :: 
        ((exists i :: 0 <= i < |ar1| && ar1[i] == val) && 
         (forall j :: 0 <= j < |ar2| ==> ar2[j] != val)) ==>
        (exists k :: 0 <= k < |result| && result[k] == val)
    
    // Completeness: result contains exactly the values that should be there
    ensures forall val :: 
        (val in result) <==> 
        (val in ar1 && val !in ar2)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): [construct sorted unique result inserting non-ar2 elements with triggers on quantified invariants] */
  result := [];
  var i := 0;
  while i < |ar1|
    decreases |ar1| - i
    invariant 0 <= i <= |ar1|
    invariant forall k :: 0 <= k < |result| ==> (exists j :: 0 <= j < i && ar1[j] == result[k])
    invariant forall k :: 0 <= k < |result| ==> forall l :: 0 <= l < |ar2| ==> result[k] != ar2[l]
    invariant forall p, q :: 0 <= p < q < |result| ==> result[p] <= result[q]
    invariant forall p, q :: 0 <= p < q < |result| ==> result[p] != result[q]
    invariant forall v {:trigger exists j :: 0 <= j < i && ar1[j] == v} :: ( (exists j :: 0 <= j < i && ar1[j] == v) && (forall l :: 0 <= l < |ar2| ==> ar2[l] != v) ) ==> (exists k :: 0 <= k < |result| && result[k] == v)
  {
    var x := ar1[i];
    if x !in ar2 && !(exists k :: 0 <= k < |result| && result[k] == x) {
      var pos := 0;
      while pos < |result| && result[pos] <= x
        decreases |result| - pos
        invariant 0 <= pos <= |result|
        invariant forall t :: 0 <= t < pos ==> result[t] <= x
      {
        pos := pos + 1;
      }
      result := result[..pos] + [x] + result[pos..];
    }
    i := i + 1;
  }
  InvariantToPost(ar1, ar2, result, i);
}

// </vc-code>
