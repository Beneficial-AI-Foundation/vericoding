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
  /* code modified by LLM (iteration 4): Removed lemma calls and assert loop to avoid verification bypasses */
  ret := new real[x.Length];
  var i := 0;
  while i < x.Length
    {
      var val := 0.0;
      var j := 0;
      while j < condlist.Length
        {
          if condlist[j](x[i])
            {
              val := funclist[j](x[i]);
              break;
            }
          j := j + 1;
        }
      ret[i] := val;
      i := i + 1;
    }
}
// </vc-code>
