predicate ValidInput(x: int) {
    1 <= x <= 3000
}

predicate CorrectOutput(x: int, result: string) {
    (x < 1200 ==> result == "ABC\n") &&
    (x >= 1200 ==> result == "ARC\n")
}

// <vc-helpers>
lemma ValidateOutputEquivalence(x: int, result: string)
  requires (x < 1200 && result == "ABC\n") || (x >= 1200 && result == "ARC\n")
  ensures CorrectOutput(x, result)
{
  if x < 1200 {
    assert result == "ABC\n";
    assert CorrectOutput(x, result);
  } else {
    assert x >= 1200;
    assert result == "ARC\n";
    assert CorrectOutput(x, result);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: string)
    requires ValidInput(x)
    ensures CorrectOutput(x, result)
// </vc-spec>
// <vc-code>
{
  var resultString: string;
  if x < 1200 {
    resultString := "ABC\n";
  } else {
    resultString := "ARC\n";
  }
  result := resultString;
  ValidateOutputEquivalence(x, result);
}
// </vc-code>

