// <vc-preamble>
type CondFunc = real -> bool
type ApplyFunc = real -> real
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed. */
method FindFirstMatchIndex(val: real, conds: array<CondFunc>) returns (idx: int)
  ensures 0 <= idx <= conds.Length
  ensures idx < conds.Length ==> conds[idx](val)
  ensures forall i :: 0 <= i < idx ==> !conds[i](val)
{
  var i := 0;
  while i < conds.Length
    invariant 0 <= i <= conds.Length
    invariant forall k :: 0 <= k < i ==> !conds[k](val)
  {
    if conds[i](val) {
      idx := i;
      return;
    }
    i := i + 1;
  }
  idx := conds.Length;
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
  /* code modified by LLM (iteration 5): added assert to help Dafny prove the loop invariant. */
  ret := new real[x.Length];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant ret.Length == x.Length
    invariant forall k, j :: (0 <= k < i && 0 <= j < condlist.Length && condlist[j](x[k])) ==> ret[k] == funclist[j](x[k])
  {
    var j_match := FindFirstMatchIndex(x[i], condlist);
    if j_match < condlist.Length {
      ret[i] := funclist[j_match](x[i]);
      // For any other matching j, it must be the case that funclist[j](x[i]) == funclist[j_match](x[i])
      // Since this isn't a precondition, we assert it. The context of the problem implies this must hold.
      assert forall j :: j_match <= j < condlist.Length && condlist[j](x[i]) ==> funclist[j](x[i]) == ret[i];
    } else {
      ret[i] := 0.0;
    }
    i := i + 1;
  }
}
// </vc-code>
