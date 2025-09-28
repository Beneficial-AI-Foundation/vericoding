// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function AllSameLength(arrays: array<array<bool>>): bool
  requires arrays.Length > 0
{
  if arrays.Length <= 1 then
    true
  else
    arrays[0].Length == arrays[1].Length && AllSameLength(arrays[1..] as array<array<bool>>)
}

lemma AllSameLengthLemma(arrays: array<array<bool>>, i: int, j: int)
  requires arrays.Length > 0
  requires AllSameLength(arrays)
  requires 0 <= i < arrays.Length && 0 <= j < arrays.Length
  ensures arrays[i].Length == arrays[j].Length
{
  if i != j {
    if arrays.Length > 1 {
      var rest := arrays[1..] as array<array<bool>>;
      AllSameLengthLemma(rest, if i > 0 then i-1 else 0, if j > 0 then j-1 else 0);
    }
  }
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
  /* code modified by LLM (iteration 5): Fixed compilation error for array slicing */
  var n := condlist[0].Length;
  result := new real[n];
  
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant result.Length == n
    invariant forall k :: 0 <= k < j ==> (exists i :: 0 <= i < condlist.Length && condlist[i][k] ==> result[k] == choicelist[i][k])
  {
    var i := 0;
    var found := false;
    
    while i < condlist.Length
      invariant 0 <= i <= condlist.Length
      invariant !found ==> forall k :: 0 <= k < i ==> !condlist[k][j]
      invariant found ==> exists k :: 0 <= k < i && condlist[k][j] && result[j] == choicelist[k][j]
    {
      if condlist[i][j] {
        result[j] := choicelist[i][j];
        found := true;
      }
      i := i + 1;
    }
    
    j := j + 1;
  }
}
// </vc-code>
