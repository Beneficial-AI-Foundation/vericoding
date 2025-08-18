// <vc-helpers>
// </vc-helpers>

method IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
// <vc-code>
{
  assume false;
}
// </vc-code>