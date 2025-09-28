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
/* code modified by LLM (iteration 2): Fixed loop invariant and postcondition proof */
{
  var n := condlist[0].Length;
  result := new real[n];
  
  for j := 0 to n
    invariant 0 <= j <= n
    invariant forall k :: 0 <= k < j ==> 
      (exists i :: 0 <= i < condlist.Length && condlist[i][k] && result[k] == choicelist[i][k]) ||
      (forall i :: 0 <= i < condlist.Length ==> !condlist[i][k])
    invariant forall i, k :: 0 <= i < condlist.Length && 0 <= k < j && condlist[i][k] ==> 
      result[k] == choicelist[i][k]
  {
    var i := 0;
    while i < condlist.Length && !condlist[i][j]
      invariant 0 <= i <= condlist.Length
      invariant forall k :: 0 <= k < i ==> !condlist[k][j]
    {
      i := i + 1;
    }
    
    if i < condlist.Length {
      result[j] := choicelist[i][j];
    } else {
      result[j] := 0.0;
    }
  }
}
// </vc-code>
