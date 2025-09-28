// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Predicate to check if an array contains a value */
predicate Contains(arr: array<real>, value: real)
{
    exists i :: 0 <= i < arr.Length && arr[i] == value
}

/* helper modified by LLM (iteration 5): Function to convert a set to an array */
function SetToArray(s: set<real>): array<real>
{
    if s.Cardinality == 0 then new real[0] else new real[s.Cardinality](_ => s.Any())
}
// </vc-helpers>

// <vc-spec>
method Intersect(a: array<real>, b: array<real>) returns (result: array<real>)
    ensures
        result.Length < a.Length && result.Length < b.Length &&
        forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> (
            (a[i] == b[j] ==> exists k :: 0 <= k < result.Length && result[k] == a[i]) &&
            (a[i] != b[j] ==> !exists k :: 0 <= k < result.Length && result[k] == a[i])
        )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors in the for loop for set iteration */
{
    var commonElements: set<real> := {};
    for i := 0 to a.Length - 1
        invariant 0 <= i <= a.Length
        invariant forall x :: x in commonElements ==> Contains(a, x) && Contains(b, x)
    {
        if Contains(b, a[i]) {
            commonElements := commonElements + {a[i]};
        }
    }

    result := new real[commonElements.Cardinality()];
    var k := 0;
    if commonElements.Cardinality() > 0 {
        // Iterate over the set and populate the result array.
        // Note: Dafny's built-in sets do not have a defined iteration order.
        // For deterministic behavior or specific ordering, a different approach might be needed.
        // Assuming any order is acceptable for populating the result array from the set.
        var commonElementsArray := SetToArray(commonElements);
        for i := 0 to commonElementsArray.Length - 1 {
            result[k] := commonElementsArray[i];
            k := k + 1;
        }
    }
}
// </vc-code>
