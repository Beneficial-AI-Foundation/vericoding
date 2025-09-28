// <vc-preamble>
predicate ValidInput(s: string) {
    |s| == 3 && forall i :: 0 <= i < |s| ==> s[i] == 'S' || s[i] == 'R'
}

function MaxConsecutiveRainyDays(s: string): int
    requires ValidInput(s)
{
    if s == "RRR" then 3
    else if s[0..2] == "RR" || s[1..3] == "RR" then 2
    else if 'R' in s then 1
    else 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed */
// No helpers needed for this problem
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: int)
    requires ValidInput(input)
    ensures result == MaxConsecutiveRainyDays(input)
    ensures 0 <= result <= 3
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed ambiguity in boolean expression */
{
  if input == "RRR" {
    result := 3;
  } else if (input[0] == 'R' && input[1] == 'R') || (input[1] == 'R' && input[2] == 'R') {
    result := 2;
  } else if input[0] == 'R' || input[1] == 'R' || input[2] == 'R' {
    result := 1;
  } else {
    result := 0;
  }
}
// </vc-code>
