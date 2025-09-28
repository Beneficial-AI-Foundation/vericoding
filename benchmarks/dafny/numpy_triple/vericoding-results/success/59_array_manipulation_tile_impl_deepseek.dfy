// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma TileLemma<T>(A: seq<T>, reps: nat, i: int, n: int)
  requires 0 <= i < |A| * reps
  requires |A| > 0
  requires n == |A|
  ensures (i % n) < n
  ensures (i % n) >= 0
{
  /* helper modified by LLM (iteration 3): Added modulo bounds proof */
  var m := i % n;
  assert 0 <= m < n;
}
// </vc-helpers>

// <vc-spec>
method tile<T>(A: seq<T>, reps: nat) returns (result: seq<T>)
  // Number of repetitions must be positive
  requires reps > 0
  // Result length is the product of input length and repetitions
  ensures |result| == |A| * reps
  // Each element in result corresponds to the element at the appropriate position in the input
  // using modular arithmetic to cycle through the input array (only when input is non-empty)
  ensures |A| > 0 ==> forall i :: 0 <= i < |result| ==> result[i] == A[i % |A|]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed result length invariant */
  if |A| == 0 {
    result := [];
    assert |result| == 0 == |A| * reps;
  } else {
    result := [];
    var n := |A|;
    var index := 0;
    
    while index < |A| * reps
      invariant index >= 0
      invariant |result| == index
      invariant index <= |A| * reps
      invariant forall j :: 0 <= j < index ==> result[j] == A[j % n]
    {
      result := result + [A[index % n]];
      index := index + 1;
    }
  }
}
// </vc-code>
