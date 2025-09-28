// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added helper to verify consistent choices for each j */
function method ConsistentChoices(condlist: array<array<bool>>, choicelist: array<array<real>>, j: int): bool
    requires 0 <= j < condlist[0].Length
    reads condlist, choicelist
{
    forall i1, i2 :: 0 <= i1 < condlist.Length && 0 <= i2 < condlist.Length && condlist[i1][j] && condlist[i2][j] ==> choicelist[i1][j] == choicelist[i2][j]
}
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
  /* code modified by LLM (iteration 2): verify consistent choices before setting result */
  var n := condlist[0].Length;
  result := new real[n];
  for j := 0 to n - 1
  {
    assert ConsistentChoices(condlist, choicelist, j);
    var found := false;
    var val := 0.0;
    for i := 0 to condlist.Length - 1
    {
      if condlist[i][j] && !found
      {
        val := choicelist[i][j];
        found := true;
      }
    }
    result[j] := val;
  }
}
// </vc-code>
