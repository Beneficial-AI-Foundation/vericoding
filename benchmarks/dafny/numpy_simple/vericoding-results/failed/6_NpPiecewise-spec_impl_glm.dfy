// <vc-preamble>
type CondFunc = real -> bool
type ApplyFunc = real -> real
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed while loop syntax by removing 'do' keyword */
method FindFirstTrueCondition(x: real, condlist: array<CondFunc>, funclist: array<ApplyFunc>) returns (ret: int)
    requires condlist.Length == funclist.Length
    requires 0 < condlist.Length
    ensures -1 <= ret < condlist.Length
    ensures 0 <= ret ==> condlist[ret](x)
    ensures 0 <= ret ==> forall j :: 0 <= j < ret ==> !condlist[j](x)
    ensures ret == -1 ==> forall j :: 0 <= j < condlist.Length ==> !condlist[j](x)
{
    var i := 0;
    while i < condlist.Length
        invariant 0 <= i <= condlist.Length
        invariant forall j :: 0 <= j < i ==> !condlist[j](x)
    {
        if condlist[i](x) {
            return i;
        }
        i := i + 1;
    }
    return -1;
}
// </vc-helpers>

// <vc-spec>
method Piecewise(x: array<real>, condlist: array<CondFunc>, funclist: array<ApplyFunc>) returns (ret: array<real>)
    requires condlist.Length == funclist.Length
    ensures ret.Length == x.Length
    ensures forall i, j :: (0 <= i < x.Length && 0 <= j < condlist.Length && 
        condlist[j](x[i])) ==> ret[i] == funclist[j](x[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): preserved implementation from iteration 4 */
    ret := new real[x.Length];
    for i := 0 to x.Length
        invariant 0 <= i <= x.Length
        invariant forall j :: 0 <= j < i ==> 
            (exists k :: 0 <= k < condlist.Length && condlist[k](x[j]) ==> ret[j] == funclist[k](x[j]))
    {
        if condlist.Length > 0 {
            var idx := FindFirstTrueCondition(x[i], condlist, funclist);
            if idx >= 0 {
                ret[i] := funclist[idx](x[i]);
            }
        }
        // else: condlist is empty, so no condition, leave as 0.0
    }
}
// </vc-code>
