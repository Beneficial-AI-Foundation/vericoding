// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): direct equality accessor */
function EqAt(x1: seq<string>, x2: seq<string>, i: int): bool
  requires 0 <= i < |x1| && |x1| == |x2|
{
  x1[i] == x2[i]
}

// </vc-helpers>

// <vc-spec>
method Equal(x1: seq<string>, x2: seq<string>) returns (result: seq<bool>)
  requires |x1| == |x2|
  ensures |result| == |x1|
  ensures |result| == |x2|
  // Core property: result[i] = (x1[i] == x2[i]) for all valid indices
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] == x2[i])
  // Equivalence: result[i] is true if and only if strings are equal
  ensures forall i :: 0 <= i < |result| ==> (result[i] <==> x1[i] == x2[i])
  // Reflexivity: if input sequences are identical, all result elements are true
  ensures x1 == x2 ==> (forall i :: 0 <= i < |result| ==> result[i] == true)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): iterative construction with proper punctuation */
  var i := 0;
  result := [];
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == (x1[j] == x2[j])
  {
    result := result + [x1[i] == x2[i]];
    i := i + 1;
  }
}

// </vc-code>
