// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function range(n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else range(n-1) + [n-1]
}

lemma range_lemma(n: nat)
  ensures |range(n)| == n
  ensures forall i :: 0 <= i < n ==> range(n)[i] == i
{
  if n == 0 {
  } else {
    range_lemma(n-1);
  }
}

// </vc-helpers>

// <vc-spec>
method vstack(a: seq<real>, b: seq<real>) returns (result: seq<seq<real>>)
    // Input vectors must have the same length
    requires |a| == |b|
    
    // Result is a 2x n matrix where n is the length of input vectors
    ensures |result| == 2
    ensures |result[0]| == |a|
    ensures |result[1]| == |b|
    
    // First row of result equals first input vector
    ensures forall j :: 0 <= j < |a| ==> result[0][j] == a[j]
    
    // Second row of result equals second input vector  
    ensures forall j :: 0 <= j < |b| ==> result[1][j] == b[j]
// </vc-spec>
// <vc-code>
{
  var n := |a|;
  var row1: seq<real> := a;
  var row2: seq<real> := b;
  result := [row1, row2];
  range_lemma(n);
}
// </vc-code>
