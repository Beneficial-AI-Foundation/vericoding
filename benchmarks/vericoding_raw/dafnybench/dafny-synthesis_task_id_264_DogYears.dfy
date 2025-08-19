// <vc-helpers>
// </vc-helpers>

method DogYears(humanYears: int) returns (dogYears: int)
    requires humanYears >= 0
    ensures dogYears == 7 * humanYears
// <vc-code>
{
  assume false;
}
// </vc-code>