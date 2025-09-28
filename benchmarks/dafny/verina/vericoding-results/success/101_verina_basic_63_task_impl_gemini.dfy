// <vc-preamble>
function AbsDiff(a: int, b: int): int
{
    if a >= b then a - b else b - a
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [add lemma for AbsDiff symmetry to prove postcondition] */
lemma AbsDiff_symmetric(a: int, b: int)
  ensures AbsDiff(a, b) == AbsDiff(b, a)
{}
// </vc-helpers>

// <vc-spec>
method HasCloseElements(numbers: array<int>, threshold: int) returns (result: bool)
    requires threshold >= 0
    ensures
        !result <==> (forall i: int, j: int :: 
            0 <= i < numbers.Length && 0 <= j < numbers.Length && i != j ==> 
            AbsDiff(numbers[i], numbers[j]) >= threshold)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [added loop invariants to prove postcondition] */
  result := false;
  for i := 0 to numbers.Length
    invariant forall k :: 0 <= k < i ==> (forall l :: k < l < numbers.Length ==> AbsDiff(numbers[k], numbers[l]) >= threshold)
  {
    for j := i + 1 to numbers.Length
      invariant forall k :: 0 <= k < i ==> (forall l :: k < l < numbers.Length ==> AbsDiff(numbers[k], numbers[l]) >= threshold)
      invariant forall l :: i < l < j ==> AbsDiff(numbers[i], numbers[l]) >= threshold
    {
      if AbsDiff(numbers[i], numbers[j]) < threshold {
        result := true;
        return;
      }
    }
  }
}
// </vc-code>
