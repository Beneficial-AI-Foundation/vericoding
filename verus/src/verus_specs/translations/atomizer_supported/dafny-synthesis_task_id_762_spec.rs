pub fn IsMonthWith30Days(month: i32) -> (result: bool)
    requires(1 <= month <= 12)
    ensures(result <==> (month == 4 || month == 6 || month == 9 || month == 11))
{
}