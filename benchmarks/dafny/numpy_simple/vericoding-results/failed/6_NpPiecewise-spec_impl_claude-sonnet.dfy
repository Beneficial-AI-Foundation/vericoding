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
  /* code modified by LLM (iteration 5): fix loop invariant by ensuring ret[i] is initialized before loop invariant check */
  ret := new real[x.Length];
  for i := 0 to x.Length
    invariant 0 <= i <= x.Length
    invariant ret.Length == x.Length
    invariant forall ii, jj :: (0 <= ii < i && 0 <= jj < condlist.Length && condlist[jj](x[ii])) ==> ret[ii] == funclist[jj](x[ii])
  {
    ret[i] := 0.0;
    for j := 0 to condlist.Length
      invariant 0 <= j <= condlist.Length
      invariant forall jj :: (0 <= jj < j && condlist[jj](x[i])) ==> ret[i] == funclist[jj](x[i])
    {
      if condlist[j](x[i]) {
        ret[i] := funclist[j](x[i]);
        break;
      }
    }
  }
}
// </vc-code>
