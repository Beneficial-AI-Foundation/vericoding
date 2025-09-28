// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 3): Implement np.select logic using found flag to select the first true condition for each position */
  result := new real[condlist[0].Length];
  for j := 0 to result.Length - 1 {
    var val := 0.0;
    var found := false;
    for i := 0 to condlist.Length - 1 {
      if condlist[i][j] && !found {
        val := choicelist[i][j];
        found := true;
      }
    }
    result[j] := val;
  }
}
// </vc-code>
