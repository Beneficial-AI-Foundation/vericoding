// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): basic min function for integers */
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method select(condlist: array<array<bool>>, choicelist: array<array<real>>) returns (result: array<real>)
    requires 
        condlist.Length > 0 &&
        condlist.Length == choicelist.Length &&
        (forall i :: 0 <= i < condlist.Length ==> condlist[i].Length > 0) &&
        (forall i :: 0 <= i < condlist.Length ==> condlist[i].Length == choicelist[i].Length) &&
        (forall i, j :: 0 <= i < condlist.Length && 0 <= j < condlist.Length ==> 
            condlist[i].Length == condlist[j].Length)
    ensures
        result.Length == condlist[0].Length &&
        (forall i, j :: 
            0 <= i < condlist.Length && 0 <= j < result.Length && condlist[i][j] ==> 
            result[j] == choicelist[i][j])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): removed writes to input arrays; allocate and initialize result */
  result := new real[condlist[0].Length];
  var j := 0;
  while j < result.Length
    invariant 0 <= j <= result.Length
    decreases result.Length - j
  {
    result[j] := 0.0;
    j := j + 1;
  }
}
// </vc-code>
