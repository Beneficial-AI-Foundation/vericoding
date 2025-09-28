// <vc-preamble>
// Constructs a 2x2 block matrix from four equal-sized vectors and returns the flattened result
// </vc-preamble>

// <vc-helpers>
function lengthEqual(a: seq<real>, b: seq<real>, c: seq<real>, d: seq<real>): bool
  ensures lengthEqual(a, b, c, d) <==> |a| == |b| && |b| == |c| && |c| == |d|
{
  |a| == |b| && |b| == |c| && |c| == |d|
}

lemma BlockMatrixLemma(tl: seq<real>, tr: seq<real>, bl: seq<real>, br: seq<real>, result: seq<real>, offset: int)
  requires |tl| == |tr| == |bl| == |br|
  requires |result| == 4 * |tl|
  requires offset >= 0
  requires offset + |tl| <= |result|
  requires forall i :: 0 <= i < |tl| ==> result[offset + i] == tl[i]
  ensures forall i :: 0 <= i < |tl| ==> result[offset + i] == tl[i]
{
}

/* helper modified by LLM (iteration 4): Strengthened lemma with stronger postcondition */
// </vc-helpers>

// <vc-spec>
method bmat(topLeft: seq<real>, topRight: seq<real>, bottomLeft: seq<real>, bottomRight: seq<real>) 
    returns (result: seq<real>)
    // All input vectors must have the same length
    requires |topLeft| == |topRight|
    requires |topLeft| == |bottomLeft| 
    requires |topLeft| == |bottomRight|
    // Result has length 4 times the input vector length
    ensures |result| == 4 * |topLeft|
    // First block: elements 0 to n-1 come from topLeft
    ensures forall i :: 0 <= i < |topLeft| ==> result[i] == topLeft[i]
    // Second block: elements n to 2n-1 come from topRight
    ensures forall i :: 0 <= i < |topRight| ==> result[i + |topLeft|] == topRight[i]
    // Third block: elements 2n to 3n-1 come from bottomLeft
    ensures forall i :: 0 <= i < |bottomLeft| ==> result[i + 2 * |topLeft|] == bottomLeft[i]
    // Fourth block: elements 3n to 4n-1 come from bottomRight
    ensures forall i :: 0 <= i < |bottomRight| ==> result[i + 3 * |topLeft|] == bottomRight[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Added necessary assertions to help verification */
{
  var n := |topLeft|;
  result := [];
  
  // Add topLeft block (first n elements)
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == topLeft[j]
  {
    result := result + [topLeft[i]];
    i := i + 1;
  }
  assert |result| == n;
  assert forall j :: 0 <= j < n ==> result[j] == topLeft[j];
  
  // Add topRight block (next n elements: n to 2n-1)
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == n + i
    invariant forall j :: 0 <= j < n ==> result[j] == topLeft[j]
    invariant forall k :: 0 <= k < i ==> result[n + k] == topRight[k]
  {
    result := result + [topRight[i]];
    i := i + 1;
  }
  assert |result| == 2*n;
  assert forall j :: 0 <= j < n ==> result[j] == topLeft[j];
  assert forall k :: 0 <= k < n ==> result[n + k] == topRight[k];
  
  // Add bottomLeft block (next n elements: 2n to 3n-1)
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == 2*n + i
    invariant forall j :: 0 <= j < n ==> result[j] == topLeft[j]
    invariant forall j :: 0 <= j < n ==> result[n + j] == topRight[j]
    invariant forall k :: 0 <= k < i ==> result[2*n + k] == bottomLeft[k]
  {
    result := result + [bottomLeft[i]];
    i := i + 1;
  }
  assert |result| == 3*n;
  assert forall j :: 0 <= j < n ==> result[j] == topLeft[j];
  assert forall j :: 0 <= j < n ==> result[n + j] == topRight[j];
  assert forall k :: 0 <= k < n ==> result[2*n + k] == bottomLeft[k];
  
  // Add bottomRight block (last n elements: 3n to 4n-1)
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == 3*n + i
    invariant forall j :: 0 <= j < n ==> result[j] == topLeft[j]
    invariant forall j :: 0 <= j < n ==> result[n + j] == topRight[j]
    invariant forall j :: 0 <= j < n ==> result[2*n + j] == bottomLeft[j]
    invariant forall k :: 0 <= k < i ==> result[3*n + k] == bottomRight[k]
  {
    result := result + [bottomRight[i]];
    i := i + 1;
  }
  assert |result| == 4*n;
}
// </vc-code>
