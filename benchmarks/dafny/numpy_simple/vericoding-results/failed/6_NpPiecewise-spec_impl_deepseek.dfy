// <vc-preamble>
type CondFunc = real -> bool
type ApplyFunc = real -> real
// </vc-preamble>

// <vc-helpers>

function AndCond(c1: CondFunc, c: CondFunc): CondFunc {
  x => c1(x) && c(x)
}

function Identity(r: real): real {
  r
}

predicate CondAt(condlist: array<CondFunc>, j: int, x: real) 
  requires 0 <= j < condlist.Length
  reads condlist {
  condlist[j](x)
}

function FuncResult(funclist: array<ApplyFunc>, j: int, x: real): real
  requires 0 <= j < funclist.Length
  reads funclist {
  funclist[j](x)
}

lemma /* helper modified by LLM (iteration 5): Strengthened lemma to handle array access bounds */
Lemma_ForallPreserved(ret: array<real>, x: array<real>, condlist: array<CondFunc>, funclist: array<ApplyFunc>, idx: int, old_idx: int)
  requires 0 <= old_idx <= idx <= x.Length
  requires ret.Length == x.Length
  requires condlist.Length == funclist.Length
  requires forall i, j :: (0 <= i < old_idx && 0 <= j < condlist.Length && condlist[j](x[i])) ==> ret[i] == funclist[j](x[i])
  ensures forall i, j :: (0 <= i < idx && 0 <= j < condlist.Length && condlist[j](x[i])) ==> ret[i] == funclist[j](x[i])
{
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
  /* code modified by LLM (iteration 5): Fixed array access bounds and loop invariant */
  ret := new real[x.Length];
  var idx := 0;
  
  while idx < x.Length
    invariant 0 <= idx <= x.Length
    invariant ret.Length == x.Length
    invariant forall i, j :: (0 <= i < idx && 0 <= j < condlist.Length && condlist[j](x[i])) ==> ret[i] == funclist[j](x[i])
  {
    ret[idx] := x[idx]; // Default value
    var j := 0;
    var found := false;
    
    while j < condlist.Length
      invariant 0 <= j <= condlist.Length
      invariant !found ==> forall k :: 0 <= k < j ==> !condlist[k](x[idx])
      invariant found ==> exists k :: 0 <= k < j && condlist[k](x[idx]) && ret[idx] == funclist[k](x[idx])
    {
      if condlist[j](x[idx]) && !found {
        ret[idx] := funclist[j](x[idx]);
        found := true;
      }
      j := j + 1;
    }
    
    idx := idx + 1;
    Lemma_ForallPreserved(ret, x, condlist, funclist, idx, idx - 1);
  }
}
// </vc-code>
