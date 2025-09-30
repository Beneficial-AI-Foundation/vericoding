

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CalculateLoss(costPrice: int, sellingPrice: int) returns (loss: int)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
// </vc-spec>
// <vc-code>
{
  if costPrice > sellingPrice {
    loss := costPrice - sellingPrice;
  } else {
    loss := 0;
  }
}
// </vc-code>

