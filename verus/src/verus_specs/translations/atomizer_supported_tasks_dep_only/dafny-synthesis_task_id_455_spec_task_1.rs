pub fn MonthHas31Days(month: int) -> (result: bool)
    requires(1 <= month <= 12)
    ensures(result <==> month in {1, 3, 5, 7, 8, 10, 12})
{
}