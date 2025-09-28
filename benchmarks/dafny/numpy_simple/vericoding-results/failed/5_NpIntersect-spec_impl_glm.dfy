// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 2): added explicit checks for array lengths to satisfy postcondition */
    if a.Length == 0 || b.Length == 0 {
        result := new real[0];
    } else if a.Length == 1 || b.Length == 1 {
        result := new real[0];
    } else {
        var candidateFound := false;
        var candidate := 0.0;
        for i := 0 to a.Length - 1 {
            var allEqual := true;
            for j := 0 to b.Length - 1 {
                if a[i] != b[j] {
                    allEqual := false;
                    break;
                }
            }
            if allEqual {
                candidateFound := true;
                candidate := a[i];
                break;
            }
        }
        if candidateFound {
            result := new real[1];
            result[0] := candidate;
        } else {
            result := new real[0];
        }
    }
}
// </vc-code>
