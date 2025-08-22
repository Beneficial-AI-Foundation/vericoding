//IMPL
method select (condlist: array<array<bool>>, choicelist: array<array<real>>) returns (ret: array<real>)
    requires condlist.Length > 0 && choicelist.Length > 0
    requires condlist.Length == choicelist.Length 
    requires forall i :: 0 <= i < condlist.Length ==> condlist[i].Length == condlist[0].Length && choicelist[i].Length == condlist[0].Length
    ensures ret.Length == condlist[0].Length
    ensures forall i, j :: 0 <= i < condlist.Length && 0 <= j < condlist[0].Length ==>  condlist[i][j] ==> ret[j] == choicelist[i][j]
{
    ret := new real[condlist[0].Length];
    
    /* code modified by LLM (iteration 3): Fixed loop bounds to use proper array indexing and corrected loop syntax */
    var j := 0;
    while j < condlist[0].Length
        invariant 0 <= j <= condlist[0].Length
        invariant forall i, k :: 0 <= i < condlist.Length && 0 <= k < j ==> condlist[i][k] ==> ret[k] == choicelist[i][k]
    {
        /* code modified by LLM (iteration 3): Changed to while loop with proper bounds checking */
        var i := 0;
        while i < condlist.Length
            invariant 0 <= i <= condlist.Length
            invariant forall k :: 0 <= k < i && condlist[k][j] ==> ret[j] == choicelist[k][j]
        {
            if condlist[i][j] {
                ret[j] := choicelist[i][j];
            }
            i := i + 1;
        }
        j := j + 1;
    }
}