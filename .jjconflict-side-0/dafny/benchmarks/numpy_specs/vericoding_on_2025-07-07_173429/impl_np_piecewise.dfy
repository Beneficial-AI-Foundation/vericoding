//IMPL
method piecewise(x: array<real>, condlist: array<real -> bool>, funclist: array<real -> real>) returns (ret: array<real>)
    requires condlist.Length == funclist.Length;
    ensures ret.Length == x.Length;
    ensures forall i, j :: 0 <= i < x.Length && 0 <= j < condlist.Length ==> if condlist[j](x[i]) then ret[i] == funclist[j](x[i]) else true;
{
    ret := new real[x.Length];
    
    /* code modified by LLM (iteration 4): Simplified approach without problematic assertions */
    var i := 0;
    while i < x.Length
        invariant 0 <= i <= x.Length;
        invariant ret.Length == x.Length;
        invariant forall k, j :: 0 <= k < i && 0 <= j < condlist.Length ==> if condlist[j](x[k]) then ret[k] == funclist[j](x[k]) else true;
    {
        /* code modified by LLM (iteration 4): Find first matching condition and apply it */
        var j := 0;
        var found := false;
        
        while j < condlist.Length && !found
            invariant 0 <= j <= condlist.Length;
            invariant !found ==> forall l :: 0 <= l < j ==> !condlist[l](x[i]);
        {
            if condlist[j](x[i]) {
                ret[i] := funclist[j](x[i]);
                found := true;
            } else {
                j := j + 1;
            }
        }
        
        /* code modified by LLM (iteration 4): If no condition matches, set default value */
        if !found {
            ret[i] := 0.0;
        }
        
        i := i + 1;
    }
}