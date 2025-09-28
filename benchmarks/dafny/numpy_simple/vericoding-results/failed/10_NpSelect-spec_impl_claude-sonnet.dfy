// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Simplified implementation without helper function */
// </vc-helpers>

// <vc-spec>
method select(condlist: array<array<bool>>, choicelist: array<array<real>>) returns (result: array<real>)
    requires 
        condlist.Length > 0 &&
        condlist.Length == choicelist.Length &&
        (forall i :: 0 <= i < condlist.Length ==> condlist[i].Length > 0) &&
        (forall i :: 0 <= i < condlist.Length ==> condlist[i].Length == choicelist[i].Length) &&
        (forall i, j :: 0 <= i < condlist.Length && 0 <= j < condlist.Length ==> 
            condlist[i].Length == condlist[j].Length)
    ensures
        result.Length == condlist[0].Length &&
        (forall i, j :: 
            0 <= i < condlist.Length && 0 <= j < result.Length && condlist[i][j] ==> 
            result[j] == choicelist[i][j])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Direct implementation without helper function */
    result := new real[condlist[0].Length];
    
    for j := 0 to result.Length
        invariant 0 <= j <= result.Length
        invariant forall k :: 0 <= k < j ==> 
            (forall i :: 0 <= i < condlist.Length && condlist[i][k] ==> result[k] == choicelist[i][k])
    {
        for i := 0 to condlist.Length
            invariant 0 <= i <= condlist.Length
            invariant forall prev_i :: 0 <= prev_i < i && condlist[prev_i][j] ==> 
                (forall later_i :: prev_i < later_i < i ==> !condlist[later_i][j] || result[j] == choicelist[later_i][j])
        {
            if condlist[i][j] {
                result[j] := choicelist[i][j];
            }
        }
    }
}
// </vc-code>
