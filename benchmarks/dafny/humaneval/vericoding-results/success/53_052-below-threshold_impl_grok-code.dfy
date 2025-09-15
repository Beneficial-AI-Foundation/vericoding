// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method below_threshold(l : seq<int>, t : int) returns (b : bool)

    ensures b == (forall i : int :: i >= 0 && i < |l| ==> l[i] < t)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed loop bounds to handle empty sequences, changed upper bound from |l|-1 to |l| to ensure validity for all sequence lengths */
  b := true;
  for i := 0 to |l|
    invariant 0 <= i <= |l|
    invariant b == (forall j :: 0 <= j < i ==> l[j] < t)
  {
    b := b && (l[i] < t);
  }
}
// </vc-code>
