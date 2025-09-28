// <vc-preamble>
predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed IsDigit function signature and lemma */
function IsDigit2(c: char): bool
{
  '0' <= c <= '9'
}

lemma CountDigitsLemma(s: string, i: int, count: nat)
  requires 0 <= i <= |s|
  ensures count >= 0
{
}
// </vc-helpers>

// <vc-spec>
method CountDigits(s: string) returns (result: nat)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed IsDigit function name and while loop */
  result := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result >= 0
  {
    if IsDigit2(s[i]) {
      result := result + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
