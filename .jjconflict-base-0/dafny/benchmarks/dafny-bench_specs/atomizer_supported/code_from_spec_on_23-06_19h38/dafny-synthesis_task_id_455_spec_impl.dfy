//IMPL 
method MonthHas31Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month in {1, 3, 5, 7, 8, 10, 12}
{
    /* code modified by LLM (iteration 1): implementation remains the same as it correctly implements the specification */
    result := month in {1, 3, 5, 7, 8, 10, 12};
}