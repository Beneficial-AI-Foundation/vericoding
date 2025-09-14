// <vc-preamble>
predicate IsEven(n: int)
{
    (n % 2) == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsProductEven(arr: array<int>) returns (result: bool)
    ensures result <==> (exists k :: 0 <= k < arr.Length && IsEven(arr[k]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop invariant for `foundEven` logic */
{
    var foundEven := false;
    if arr.Length == 0 {
        return false;
    }
    for i := 0 to arr.Length
        invariant 0 <= i <= arr.Length
        invariant foundEven <==> (exists k :: 0 <= k < i && IsEven(arr[k]))
    {
        if i < arr.Length && IsEven(arr[i]) {
            foundEven := true;
            break;
        }
    }
    return foundEven;
}
// </vc-code>
