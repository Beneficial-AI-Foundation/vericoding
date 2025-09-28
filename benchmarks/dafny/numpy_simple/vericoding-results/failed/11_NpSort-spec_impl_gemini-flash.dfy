// <vc-preamble>
function MultisetCount<T(==)>(s: seq<T>, x: T): nat
{
    |set i | 0 <= i < |s| && s[i] == x|
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Sort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]) &&
        (forall x :: MultisetCount(result[..], x) == MultisetCount(a[..], x))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error: lower bound must not exceed upper bound. Removed unnecessary null check for `a`. Updated loop invariant for `j < i` to avoid index out of range error and to correctly reflect the sorted part. */
{
    result := new int[a.Length];
    for k := 0 to a.Length - 1 {
        result[k] := a[k];
    }

    var n := result.Length;
    if n == 0 {
        return;
    }

    var i := n - 1;
    while i > 0
        invariant 0 <= i < n
        invariant forall k, l :: i <= k < l < n ==> result[k] <= result[l]
        invariant forall x :: MultisetCount(result[..], x) == MultisetCount(a[..], x)
        invariant a.Length == result.Length
        decreases i
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant (forall k :: 0 <= k < j ==> result[k] <= result[j])
            invariant forall k, l :: i <= k < l < n ==> result[k] <= result[l]
            invariant forall x :: MultisetCount(result[..], x) == MultisetCount(a[..], x)
            invariant a.Length == result.Length
            decreases i - j
        {
            if result[j] > result[j+1]
            {
                var temp := result[j];
                result[j] := result[j+1];
                result[j+1] := temp;
            }
            j := j + 1;
        }
        i := i - 1;
    }
}
// </vc-code>
