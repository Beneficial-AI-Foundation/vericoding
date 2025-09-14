// <vc-preamble>
function AbsDiff(a: int, b: int): int
{
    if a >= b then a - b else b - a
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): AbsDiff properties */
predicate AbsNonNeg(a: int, b: int) { AbsDiff(a,b) >= 0 }
lemma AbsDiffSym(a: int, b: int) ensures AbsDiff(a,b) == AbsDiff(b,a) { }
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
  /* code modified by LLM (iteration 2): nested loops with invariants using !result to maintain properties */
  var n := numbers.Length;
  result := false;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant !result ==> forall p :: 0 <= p < i ==> forall q :: p < q < n ==> AbsDiff(numbers[p], numbers[q]) >= threshold
  {
    var j := i + 1;
    while j < n
      invariant 0 <= i < n
      invariant i + 1 <= j <= n
      invariant !result ==> forall p :: 0 <= p < i ==> forall q :: p < q < n ==> AbsDiff(numbers[p], numbers[q]) >= threshold
      invariant !result ==> forall q :: i < q < j ==> AbsDiff(numbers[i], numbers[q]) >= threshold
    {
      if AbsDiff(numbers[i], numbers[j]) < threshold {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>
