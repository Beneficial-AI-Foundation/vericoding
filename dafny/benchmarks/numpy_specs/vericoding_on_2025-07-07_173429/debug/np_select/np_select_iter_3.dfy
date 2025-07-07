//IMPL
method select (condlist: array<array<bool>>, choicelist: array<array<real>>) returns (ret: array<real>)
    requires condlist.Length > 0 && choicelist.Length > 0
    requires condlist.Length == choicelist.Length 
    requires forall i :: 0 <= i < condlist.Length ==> condlist[i].Length == condlist[0].Length && choicelist[i].Length == condlist[0].Length
    ensures ret.Length == condlist[0].Length
    ensures forall i, j :: 0 <= i < condlist.Length && 0 <= j < condlist[0].Length ==>  condlist[i][j] ==> ret[j] == choicelist[i][j]
{
    ret := new real[condlist[0].Length];
    
    /* code modified by LLM (iteration 2): Fixed loop syntax from 'to' to proper Dafny for-loop syntax */
    for j := 0 to condlist[0].Length
        invariant forall i, k :: 0 <= i < condlist.Length && 0 <= k < j ==> condlist[i][k] ==> ret[k] == choicelist[i][k]
    {
        for i := 0 to condlist.Length
            invariant forall k :: 0 <= k < i && condlist[k][j] ==> ret[j] == choicelist[k][j]
        {
            if condlist[i][j] {
                ret[j] := choicelist[i][j];
            }
        }
    }
}