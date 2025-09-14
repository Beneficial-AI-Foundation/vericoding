// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsK(arr: array<int>, k: int) returns (result: bool)
    ensures result == (exists i :: 0 <= i < arr.Length && arr[i] == k)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): initialize result before loop */
{
    var i: int := 0;
    var result_found: bool := false;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant result_found == (exists j :: 0 <= j < i && arr[j] == k)
    {
        if arr[i] == k {
            result_found := true;
            break;
        }
        i := i + 1;
    }
    result := result_found;
}
// </vc-code>
