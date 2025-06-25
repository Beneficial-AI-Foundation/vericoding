pub fn CalculateLoss(costPrice: int, sellingPrice: int) -> (loss: int)
    requires(costPrice >= 0 && sellingPrice >= 0)
    ensures((costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0))
{
}