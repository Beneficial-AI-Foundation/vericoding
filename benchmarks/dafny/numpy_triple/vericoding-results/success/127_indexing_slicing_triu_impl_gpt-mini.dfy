// <vc-preamble>
// Method to extract the upper triangle of a matrix relative to the k-th diagonal
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): trivial lemma to re-establish row length property */
lemma RowsHaveCols(m: seq<seq<real>>)
    requires |m| > 0
    requires forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|
    ensures forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|
{
  assert forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|;
}

// </vc-helpers>

// <vc-spec>
method Triu(m: seq<seq<real>>, k: int) returns (result: seq<seq<real>>)
    // Input matrix must be well-formed (rectangular)
    requires |m| > 0
    requires forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|
    
    // Output matrix has same dimensions as input
    ensures |result| == |m|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |m[0]|
    
    // Elements on and above the k-th diagonal are preserved
    ensures forall i, j :: 0 <= i < |m| && 0 <= j < |m[0]| && i + k <= j ==>
        result[i][j] == m[i][j]
    
    // Elements below the k-th diagonal are zeroed
    ensures forall i, j :: 0 <= i < |m| && 0 <= j < |m[0]| && i + k > j ==>
        result[i][j] == 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build result by iterating rows and columns */
  var rows := |m|;
  var cols := |m[0]|;
  var res: seq<seq<real>> := [];
  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant |res| == i
    invariant forall ii :: 0 <= ii < i ==> |res[ii]| == cols
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < cols && ii + k <= jj ==> res[ii][jj] == m[ii][jj]
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < cols && ii + k > jj ==> res[ii][jj] == 0.0
  {
    var row: seq<real> := [];
    var j := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant |row| == j
      invariant forall jj :: 0 <= jj < j ==> (if i + k <= jj then row[jj] == m[i][jj] else row[jj] == 0.0)
    {
      var v := if i + k <= j then m[i][j] else 0.0;
      row := row + [v];
      j := j + 1;
    }
    res := res + [row];
    i := i + 1;
  }
  result := res;
}

// </vc-code>
