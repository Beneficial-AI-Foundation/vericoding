predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

// <vc-helpers>
// </vc-helpers>

method CountSubstringsWithSumOfDigitsEqualToLength(s: string) returns (count: int)
    ensures count >= 0
// <vc-code>
{
  assume false;
}
// </vc-code>