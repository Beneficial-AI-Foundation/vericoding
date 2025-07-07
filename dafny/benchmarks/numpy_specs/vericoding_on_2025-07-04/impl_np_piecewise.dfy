//IMPL
method piecewise(x: array<real>, condlist: array<real -> bool>, funclist: array<real -> real>) returns (ret: array<real>)
    requires condlist.Length == funclist.Length;
    ensures ret.Length == x.Length;
    ensures forall i, j :: 0 <= i < x.Length && 0 <= j < condlist.Length ==> if condlist[j](x[i]) then ret[i] == funclist[j](x[i]) else true;
{
    ret := new real[x.Length];
    
    var i := 0;
    while i < x.Length
        invariant 0 <= i <= x.Length;
        invariant ret.Length == x.Length;
        /* code modified by LLM (iteration 4): Fixed invariant to match postcondition exactly */
        invariant forall k, j :: 0 <= k < i && 0 <= j < condlist.Length ==> if condlist[j](x[k]) then ret[k] == funclist[j](x[k]) else true;
    {
        var j := 0;
        var found := false;
        /* code modified by LLM (iteration 4): Track which condition was found */
        var foundIndex := 0;
        
        while j < condlist.Length && !found
            invariant 0 <= j <= condlist.Length;
            invariant ret.Length == x.Length;
            /* code modified by LLM (iteration 4): Invariant tracking conditions checked so far */
            invariant !found ==> forall l :: 0 <= l < j ==> !condlist[l](x[i]);
            /* code modified by LLM (iteration 4): Invariant preserving postcondition for previous elements */
            invariant forall k, l :: 0 <= k < i && 0 <= l < condlist.Length ==> if condlist[l](x[k]) then ret[k] == funclist[l](x[k]) else true;
            /* code modified by LLM (iteration 4): Track found index correctly */
            invariant found ==> (0 <= foundIndex < condlist.Length && condlist[foundIndex](x[i]));
        {
            if condlist[j](x[i]) {
                ret[i] := funclist[j](x[i]);
                found := true;
                foundIndex := j;
            } else {
                j := j + 1;
            }
        }
        
        if !found {
            ret[i] := 0.0;
        }
        
        /* code modified by LLM (iteration 4): Simplified assertion focusing on the key property */
        if found {
            assert condlist[foundIndex](x[i]);
            assert ret[i] == funclist[foundIndex](x[i]);
            /* code modified by LLM (iteration 4): For any other condition that's true, we need to ensure consistency */
            assert forall l :: 0 <= l < condlist.Length && condlist[l](x[i]) ==> ret[i] == funclist[foundIndex](x[i]);
        }
        
        i := i + 1;
    }
}