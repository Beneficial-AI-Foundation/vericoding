// <vc-preamble>
predicate IsDigitSpec(c: char) 
{
    (c as int) >= 48 && (c as int) <= 57
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replace 'function method' with 'function' to comply with function-syntax:4 */
function AllDigits(text: array<char>): bool
  reads text
{
  forall i :: 0 <= i < text.Length ==> IsDigitSpec(text[i])
}
// </vc-helpers>

// <vc-spec>
method IsInteger(text: array<char>) returns (result: bool)
    ensures result == (forall i :: 0 <= i < text.Length ==> IsDigitSpec(text[i]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterative loop to check all characters are digits */
  var all := true;
  var i := 0;
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant all == (forall j :: 0 <= j < i ==> IsDigitSpec(text[j]))
    decreases text.Length - i
  {
    all := all && IsDigitSpec(text[i]);
    i := i + 1;
  }
  result := all;
}
// </vc-code>
