// <vc-preamble>
// Method to extract the upper triangle of a matrix relative to the k-th diagonal
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): rectangularity and diagonal relation helpers */
function IsRectangular(m: seq<seq<real>>): bool
{
  |m| == 0 || (forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|)
}

/* helper modified by LLM (iteration 3): whether (i,j) is on/above the k-th diagonal */
function Upper(i: int, j: int, k: int): bool
{
  i + k <= j
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
  /* code modified by LLM (iteration 3): implement via nested while loops building rows explicitly */
  var rows := |m|;
  var cols := |m[0]|;

  result := [];

  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant |result| == i
    invariant forall ii :: 0 <= ii < i ==> |result[ii]| == cols
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < cols ==> (if ii + k <= jj then result[ii][jj] == m[ii][jj] else result[ii][jj] == 0.0)
    decreases rows - i
  {
    var row: seq<real> := [];
    var j := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant |row| == j
      invariant forall jj :: 0 <= jj < j ==> (if i + k <= jj then row[jj] == m[i][jj] else row[jj] == 0.0)
      decreases cols - j
    {
      assert 0 <= i < |m|;
      assert |m[i]| == cols;
      assert 0 <= j < |m[i]|;

      var v := if i + k <= j then m[i][j] else 0.0;
      row := row + [v];
      j := j + 1;
    }
    assert |row| == cols;
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
