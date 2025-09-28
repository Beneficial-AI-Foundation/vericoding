// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial dummy helper retained */
function Dummy(x: int): int { x }
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
  /* code modified by LLM (iteration 5): iterate rows and assign each column when the first true condition is found (avoids quantifier shadowing) */
  var n := condlist.Length;
  var m := condlist[0].Length;
  result := new real[m];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < m && condlist[ii][jj] ==> result[jj] == choicelist[ii][jj]
  {
    var j := 0;
    while j < m
      invariant 0 <= j <= m
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < m && condlist[ii][jj] ==> result[jj] == choicelist[ii][jj]
      invariant forall jj0 :: 0 <= jj0 < j && condlist[i][jj0] && (forall ii :: 0 <= ii < i ==> !condlist[ii][jj0]) ==> result[jj0] == choicelist[i][jj0]
    {
      if condlist[i][j] && (forall ii :: 0 <= ii < i ==> !condlist[ii][j]) {
        result[j] := choicelist[i][j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
