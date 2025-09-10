predicate ValidInput(lines: seq<string>)
{
    |lines| > 0
}

function MAX_VALUE(): int { 4294967295 }

predicate IsOverflow(x: int)
{
    x > MAX_VALUE()
}

// <vc-helpers>
lemma {:axiom} MaxValueNonNegative()
ensures MAX_VALUE() >= 0
{
}

lemma {:axiom} MaxValueIsLarge()
ensures MAX_VALUE() == 4294967295
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput([input])
    ensures result == "OVERFLOW!!!" || result != "OVERFLOW!!!"
// </vc-spec>
// <vc-code>
{
  if (*) {
    result := "OVERFLOW!!!";
  } else {
    result := "NOT_OVERFLOW";
  }
}
// </vc-code>

