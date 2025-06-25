pub fn IsBreakEven(costPrice: int, sellingPrice: int) -> (result: bool)
    requires(costPrice >= 0 && sellingPrice >= 0)
    ensures(result <==> costPrice == sellingPrice)
{
}