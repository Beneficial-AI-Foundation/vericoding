//ATOM
predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}


// SPEC

method CountSubstringsWithSumOfDigitsEqualToLength(s: string) returns (count: int)
  ensures count >= 0
{
}
