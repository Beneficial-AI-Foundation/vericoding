// <vc-preamble>
type CondFunc = real -> bool
type ApplyFunc = real -> real
// </vc-preamble>

// <vc-helpers>

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
  ret := new real[x.Length];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant forall k, j :: (0 <= k < i && 0 <= j < condlist.Length && condlist[j](x[k])) ==> ret[k] == funclist[j](x[k])
  {
    var j := 0;
    while j < condlist.Length
      invariant 0 <= j <= condlist.Length
      invariant forall m :: (0 <= m < j && condlist[m](x[i])) ==> ret[i] == funclist[m](x[i])
    {
      if condlist[j](x[i]) {
        ret[i] := funclist[j](x[i]);
        break;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
