//IMPL
method piecewise(x: array<real>, condlist: array<real -> bool>, funclist: array<real -> real>) returns (ret: array<real>)
    requires condlist.Length == funclist.Length;
    ensures ret.Length == x.Length;
    ensures forall i, j :: 0 <= i < x.Length && 0 <= j < condlist.Length ==> if condlist[j](x[i]) then ret[i] == funclist[j](x[i]) else true;
{
    ret := new real[x.Length];
    
    for i := 0 to x.Length
        invariant ret.Length == x.Length;
        invariant forall k, j :: 0 <= k < i && 0 <= j < condlist.Length ==> if condlist[j](x[k]) then ret[k] == funclist[j](x[k]) else true;
    {
        for j := 0 to condlist.Length
            invariant forall k, l :: 0 <= k < i && 0 <= l < condlist.Length ==> if condlist[l](x[k]) then ret[k] == funclist[l](x[k]) else true;
        {
            if condlist[j](x[i]) {
                ret[i] := funclist[j](x[i]);
                break;
            }
        }
    }
}