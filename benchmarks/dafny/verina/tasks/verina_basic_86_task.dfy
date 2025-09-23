// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method rotate(a: array<int>, offset: int) returns (result: array<int>)
    requires offset >= 0
    ensures result.Length == a.Length
    ensures a.Length == 0 ==> result.Length == 0
    ensures a.Length > 0 ==> forall i :: 0 <= i < a.Length ==> 
        result[i] == a[(i + offset) % a.Length]
// </vc-spec>
// <vc-code>
{
    result := new int[a.Length];
    if a.Length > 0 {
        var j := 0;
        while j < a.Length
            invariant 0 <= j <= a.Length
            invariant forall k :: 0 <= k < j ==> result[k] == a[(k + offset) % a.Length]
        {
            var srcIdx := (j + offset) % a.Length;
            result[j] := a[srcIdx];
            j := j + 1;
        }
    }
}
// </vc-code>
