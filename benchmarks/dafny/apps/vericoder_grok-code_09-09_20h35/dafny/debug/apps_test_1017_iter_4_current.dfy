predicate ValidInput(n: int) {
    n >= 1
}

function MaxDistributions(n: int): int
    requires ValidInput(n)
{
    if n % 3 == 0 then 2 * (n / 3) else 2 * (n / 3) + 1
}

// <vc-helpers>
lemma BodyCorrect(n: int)
  requires ValidInput(n)
{
  if n % 3 == 0 {
    var result := 2 * (n / 3);
    assert result == MaxDistributions(n);
  } else {
    var result := 2 * (n / 3) + 1;
    assert result == MaxDistributions(n);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures result == MaxDistributions(n)
// </vc-spec>
// <vc-code>
{
  if n % 3 == 0 {
    result := 2 * (n / 3);
  } else {
    result := 2 * (n / 3) + 1;
  }
}
// </vc-code>

