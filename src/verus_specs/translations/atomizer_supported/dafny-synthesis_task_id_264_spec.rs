pub fn DogYears(humanYears: int) -> (dogYears: int)
    requires(humanYears >= 0)
    ensures(dogYears == 7 * humanYears)
{
}