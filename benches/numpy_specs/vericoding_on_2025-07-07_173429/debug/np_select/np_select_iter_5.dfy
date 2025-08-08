//IMPL
method select (condlist: array<array<bool>>, choicelist: array<array<real>>) returns (ret: array<real>)
    requires condlist.Length > 0 && choicelist.Length > 0
    requires condlist.Length == choicelist.Length 
    requires forall i :: 0 <= i < condlist.Length ==> condlist[i].Length == condlist[0].Length && choicelist[i].Length == condlist[0].Length
    ensures ret.Length == condlist[0].Length
    ensures forall i, j :: 0 <= i < condlist.Length && 0 <= j < condlist[0].Length ==>  condlist[i][j] ==> ret[j] == choicelist[i][j]
{
    ret := new real[condlist[0].Length];
    
    /* code modified by LLM (iteration 4): Restructured to process each position completely and maintain proper invariants */
    var j := 0;
    while j < condlist[0].Length
        invariant 0 <= j <= condlist[0].Length
        invariant forall pos :: 0 <= pos < j ==> 
            forall i :: 0 <= i < condlist.Length && condlist[i][pos] ==> ret[pos] == choicelist[i][pos]
    {
        /* code modified by LLM (iteration 4): Process conditions in order and ensure postcondition is maintained */
        var i := 0;
        while i < condlist.Length
            invariant 0 <= i <= condlist.Length
            invariant forall k :: 0 <= k < i && condlist[k][j] ==> ret[j] == choicelist[k][j]
        {
            if condlist[i][j] {
                ret[j] := choicelist[i][j];
                /* code modified by LLM (iteration 4): Added assertion to help verification */
                assert ret[j] == choicelist[i][j];
                /* code modified by LLM (iteration 4): Added ghost code to maintain invariant for all previous true conditions */
                ghost var prev_i := 0;
                while prev_i < i
                    invariant 0 <= prev_i <= i
                    invariant condlist[prev_i][j] ==> ret[j] == choicelist[prev_i][j]
                {
                    if condlist[prev_i][j] {
                        assert choicelist[prev_i][j] == choicelist[i][j];
                    }
                    prev_i := prev_i + 1;
                }
            }
            i := i + 1;
        }
        j := j + 1;
    }
}