//IMPL
method piecewise(x: array<real>, condlist: array<real -> bool>, funclist: array<real -> real>) returns (ret: array<real>)
    requires condlist.Length == funclist.Length;
    ensures ret.Length == x.Length;
    ensures forall i, j :: 0 <= i < x.Length && 0 <= j < condlist.Length ==> if condlist[j](x[i]) then ret[i] == funclist[j](x[i]) else true;
{
    ret := new real[x.Length];
    
    /* code modified by LLM (iteration 2): Fixed loop structure and invariants to properly establish postcondition */
    var i := 0;
    while i < x.Length
        invariant 0 <= i <= x.Length;
        invariant ret.Length == x.Length;
        invariant forall k, j :: 0 <= k < i && 0 <= j < condlist.Length ==> if condlist[j](x[k]) then ret[k] == funclist[j](x[k]) else true;
    {
        /* code modified by LLM (iteration 2): Simplified logic to find first matching condition */
        var j := 0;
        var processed := false;
        
        while j < condlist.Length && !processed
            invariant 0 <= j <= condlist.Length;
            invariant !processed ==> forall l :: 0 <= l < j ==> !condlist[l](x[i]);
            invariant ret.Length == x.Length;
            invariant forall k, l :: 0 <= k < i && 0 <= l < condlist.Length ==> if condlist[l](x[k]) then ret[k] == funclist[l](x[k]) else true;
        {
            if condlist[j](x[i]) {
                ret[i] := funclist[j](x[i]);
                processed := true;
                
                /* code modified by LLM (iteration 2): Added assertion to help verification */
                assert condlist[j](x[i]) && ret[i] == funclist[j](x[i]);
            } else {
                j := j + 1;
            }
        }
        
        /* code modified by LLM (iteration 2): Handle case where no condition matches */
        if !processed {
            ret[i] := 0.0; // default value
        }
        
        /* code modified by LLM (iteration 2): Added assertion to establish postcondition for current element */
        assert forall l :: 0 <= l < condlist.Length ==> if condlist[l](x[i]) then ret[i] == funclist[l](x[i]) else true;
        
        i := i + 1;
    }
}