// <vc-preamble>
predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fix length usage to |s| and keep recursive definition */
function CountDigitsRec(s: string): nat
  decreases |s|
{
  if |s| == 0 then 0 else (if IsDigit(s[0]) then 1 else 0) + CountDigitsRec(s[1..])
}
// </vc-helpers>

// <vc-spec>
method CountDigits(s: string) returns (result: nat)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): return count from recursive helper */
  result := CountDigitsRec(s);
}
// </vc-code>
