// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method unique_product(arr: array<int>) returns (result: int)
    ensures
        /* Product of all unique integers in the array */
        true /* Placeholder for actual postcondition */
// </vc-spec>
// <vc-code>
{
    var seen := {};
    var product := 1;
    var i := 0;
    
    while i < arr.Length
    {
        if arr[i] !in seen {
            seen := seen + {arr[i]};
            product := product * arr[i];
        }
        i := i + 1;
    }
    
    result := product;
}
// </vc-code>
