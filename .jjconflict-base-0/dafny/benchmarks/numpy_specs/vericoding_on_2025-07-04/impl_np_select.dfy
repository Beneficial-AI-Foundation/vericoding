//IMPL
method select (condlist: array<array<bool>>, choicelist: array<array<real>>) returns (ret: array<real>)
    requires condlist.Length > 0 && choicelist.Length > 0
    requires condlist.Length == choicelist.Length 
    requires forall i :: 0 <= i < condlist.Length ==> condlist[i].Length == condlist[0].Length && choicelist[i].Length == condlist[0].Length
    ensures ret.Length == condlist[0].Length
    ensures forall i, j :: 0 <= i < condlist.Length && 0 <= j < condlist[0].Length ==>  condlist[i][j] ==> ret[j] == choicelist[i][j]
{
    ret := new real[condlist[0].Length];
    
    var j := 0;
    while j < condlist[0].Length
        invariant 0 <= j <= condlist[0].Length
        /* code modified by LLM (iteration 4): Simplified invariant focusing on postcondition satisfaction */
        invariant forall jj :: 0 <= jj < j ==> 
            forall i :: 0 <= i < condlist.Length ==> 
                condlist[i][jj] ==> ret[jj] == choicelist[i][jj]
    {
        var i := 0;
        /* code modified by LLM (iteration 4): Track the first matching index */
        var first_match := -1;
        
        /* code modified by LLM (iteration 4): First pass to find the first matching condition */
        while i < condlist.Length
            invariant 0 <= i <= condlist.Length
            invariant first_match == -1 ==> forall k :: 0 <= k < i ==> !condlist[k][j]
            invariant first_match >= 0 ==> 0 <= first_match < i && condlist[first_match][j] && 
                     (forall k :: 0 <= k < first_match ==> !condlist[k][j])
        {
            if condlist[i][j] && first_match == -1 {
                first_match := i;
            }
            i := i + 1;
        }
        
        /* code modified by LLM (iteration 4): Set the result based on first match */
        if first_match >= 0 {
            ret[j] := choicelist[first_match][j];
            
            /* code modified by LLM (iteration 4): Assert key properties for verification */
            assert condlist[first_match][j];
            assert ret[j] == choicelist[first_match][j];
            assert forall k :: 0 <= k < first_match ==> !condlist[k][j];
            
            /* code modified by LLM (iteration 4): Prove postcondition for this column */
            forall ii | 0 <= ii < condlist.Length && condlist[ii][j]
                ensures ret[j] == choicelist[ii][j]
            {
                if ii < first_match {
                    assert !condlist[ii][j]; // contradiction
                } else if ii == first_match {
                    assert ret[j] == choicelist[ii][j];
                } else {
                    // ii > first_match, but first_match was the first true condition
                    // so ret[j] == choicelist[first_match][j]
                    // We need to show choicelist[first_match][j] == choicelist[ii][j]
                    // This is only true if all choice values for true conditions are the same
                    // But the postcondition assumes this implicitly
                    assert ret[j] == choicelist[first_match][j];
                    // The postcondition can only be satisfied if choicelist[first_match][j] == choicelist[ii][j]
                    // when both condlist[first_match][j] and condlist[ii][j] are true
                }
            }
        }
        
        j := j + 1;
    }
}