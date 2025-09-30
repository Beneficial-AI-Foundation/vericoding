// <vc-preamble>
// Method to extract the upper triangle of a matrix
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): compute triu element value based on k-diagonal */
function TriuVal(m: seq<seq<real>>, k: int, i: int, j: int): real
  requires 0 <= i < |m|
  requires 0 <= j < |m[i]|
{
  if i > j - k then 0.0 else m[i][j]
}

/* helper modified by LLM (iteration 4): get row length of rectangular matrix */
function RowLength(m: seq<seq<real>>): int
  requires |m| > 0
{
  |m[0]|
}
// </vc-helpers>

// <vc-spec>
method Triu(m: seq<seq<real>>, k: int := 0) returns (result: seq<seq<real>>)
  // Input matrix must be rectangular (all rows have same length)
  requires |m| > 0
  requires forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|
  
  // Output has same dimensions as input
  ensures |result| == |m|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |m[0]|
  
  // Elements are preserved or zeroed according to triu rule
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
    result[i][j] == (if i > j - k then 0.0 else m[i][j])
    
  // Elements on or above k-th diagonal are preserved
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| && i <= j - k ==>
    result[i][j] == m[i][j]
    
  // Elements below k-th diagonal are zeroed
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| && i > j - k ==>
    result[i][j] == 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): iterative construction using sequence updates to avoid comprehension parse issues */
  var rows := |m|;
  var cols := |m[0]|;
  var r := m;
  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant |r| == rows
    invariant forall t :: 0 <= t < |r| ==> |r[t]| == cols
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < cols ==> r[ii][jj] == TriuVal(m, k, ii, jj)
    invariant forall ii :: i <= ii < rows ==> r[ii] == m[ii]
  {
    var row := r[i];
    var j := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant |row| == cols
      invariant forall jj :: 0 <= jj < j ==> row[jj] == TriuVal(m, k, i, jj)
      invariant forall jj :: j <= jj < cols ==> row[jj] == r[i][jj]
    {
      if i > j - k {
        row := row[j := 0.0];
      } else {
        // keep original value, which equals m[i][j]
      }
      j := j + 1;
    }
    r := r[i := row];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
