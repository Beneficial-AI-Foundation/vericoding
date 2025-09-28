// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): instantiate row length property */
lemma tril_row_length(m: seq<seq<real>>, i: int, cols: int)
  requires |m| > 0
  requires 0 <= i < |m|
  requires forall r :: 0 <= r < |m| ==> |m[r]| == cols
  ensures |m[i]| == cols
{
  assert |m[i]| == cols;
}

// </vc-helpers>

// <vc-spec>
method tril(m: seq<seq<real>>, k: int := 0) returns (result: seq<seq<real>>)
    requires |m| > 0
    requires forall i :: 0 <= i < |m| ==> |m[i]| > 0
    requires forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|  // All rows have same length
    ensures |result| == |m|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |m[0]|
    // Core property: element-wise specification
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
        result[i][j] == (if i >= j - k then m[i][j] else 0.0)
    // Sanity check: diagonal elements preserved when k = 0
    ensures k == 0 ==> 
        forall idx :: 0 <= idx < |m| && idx < |m[0]| ==>
            result[idx][idx] == m[idx][idx]
    // Sanity check: all elements preserved when k is very large
    ensures k >= |m[0]| as int ==>
        forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
            result[i][j] == m[i][j]
    // Sanity check: all elements zeroed when k is very negative
    ensures k <= -(|m| as int) ==>
        forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
            result[i][j] == 0.0
    // Shape preservation property
    ensures |result| == |m| && 
        (forall i :: 0 <= i < |result| ==> |result[i]| == |m[i]|)
    // Lower triangle preservation: elements satisfying i >= j - k are unchanged
    ensures forall i, j :: 0 <= i < |m| && 0 <= j < |m[i]| && i >= j - k ==>
        result[i][j] == m[i][j]
    // Upper triangle zeroing: elements satisfying i < j - k are set to zero
    ensures forall i, j :: 0 <= i < |m| && 0 <= j < |m[i]| && i < j - k ==>
        result[i][j] == 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build result rows with invariants ensuring shape and element-wise properties */
  var n := |m|;
  var cols := |m[0]|;
  var out: seq<seq<real>> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |out| == i
    invariant forall ii :: 0 <= ii < |out| ==> |out[ii]| == cols
    invariant forall ii, jj :: 0 <= ii < |out| && 0 <= jj < |out[ii]| ==> out[ii][jj] == (if ii >= jj - k then m[ii][jj] else 0.0)
    decreases n - i
  {
    var row: seq<real> := [];
    var j := 0;
    while j < cols
      invariant 0 <= j <= cols
      invariant |row| == j
      invariant forall jj :: 0 <= jj < |row| ==> row[jj] == (if i >= jj - k then m[i][jj] else 0.0)
      decreases cols - j
    {
      var v := if i >= j - k then m[i][j] else 0.0;
      row := row + [v];
      j := j + 1;
    }
    out := out + [row];
    i := i + 1;
  }
  result := out;
}

// </vc-code>
