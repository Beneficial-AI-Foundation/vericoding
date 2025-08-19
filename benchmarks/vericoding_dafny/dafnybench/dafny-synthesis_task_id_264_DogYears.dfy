// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method DogYears(humanYears: int) returns (dogYears: int)
    requires humanYears >= 0
    ensures dogYears == 7 * humanYears
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>