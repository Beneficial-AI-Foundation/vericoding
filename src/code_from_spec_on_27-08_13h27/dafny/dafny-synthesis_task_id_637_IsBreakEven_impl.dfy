// <vc-helpers>
// No additional helpers or proofs needed for this simple verification
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
// </vc-spec>
// </vc-spec>

// <vc-code>
method IsBreakEvenImpl(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
{
    result := costPrice == sellingPrice;
}
// </vc-code>
