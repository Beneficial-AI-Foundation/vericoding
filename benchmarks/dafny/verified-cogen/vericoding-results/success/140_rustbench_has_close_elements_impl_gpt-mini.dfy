// <vc-preamble>
function AbsSpec(i: int): int
{
    if i < 0 then -i else i
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): AbsSpec symmetry */
lemma AbsSpecSym(x: int) ensures AbsSpec(x) == AbsSpec(-x) { }
/* helper modified by LLM (iteration 2): AbsSpec non-negativity */
lemma AbsSpecNonNegative(x: int) ensures AbsSpec(x) >= 0 { }
// </vc-helpers>

// <vc-spec>
method HasCloseElements(numbers: array<int>, threshold: int) returns (flag: bool)
    requires threshold > 0
    requires forall i, j :: 0 <= i < numbers.Length && 0 <= j < numbers.Length ==> 
        numbers[i] - numbers[j] < 0x7FFFFFFF && -(numbers[i] - numbers[j]) < 0x7FFFFFFF
    ensures flag == (exists i, j :: 
        0 <= i < numbers.Length && 0 <= j < numbers.Length && 
        i != j && AbsSpec(numbers[i] - numbers[j]) < threshold)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): direct existential check for close elements */
  flag := exists i, j ::
    0 <= i < numbers.Length && 0 <= j < numbers.Length &&
    i != j && AbsSpec(numbers[i] - numbers[j]) < threshold;
}

// </vc-code>
