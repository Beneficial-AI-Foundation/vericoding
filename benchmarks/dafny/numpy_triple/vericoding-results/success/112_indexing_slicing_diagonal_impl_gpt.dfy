// <vc-preamble>
// Method to extract diagonal elements from a 2D matrix with optional offset


// Helper function to compute minimum of two integers
function Minimum(a: int, b: int): int
  ensures Minimum(a, b) == if a <= b then a else b
{
  if a <= b then a else b
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove Minimum(a,b) <= a */
lemma MinLeLeft(a: int, b: int)
  ensures Minimum(a, b) <= a
{
  if a <= b {
    assert Minimum(a, b) == a;
  } else {
    assert b <= a;
    assert Minimum(a, b) == b;
  }
}

/* helper modified by LLM (iteration 2): prove Minimum(a,b) <= b */
lemma MinLeRight(a: int, b: int)
  ensures Minimum(a, b) <= b
{
  if a <= b {
    assert Minimum(a, b) == a;
    assert a <= b;
  } else {
    assert Minimum(a, b) == b;
  }
}

/* helper modified by LLM (iteration 2): Minimum is non-negative if both args non-negative */
lemma MinNonNeg(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures 0 <= Minimum(a, b)
{
  if a <= b {
    assert Minimum(a, b) == a;
    assert 0 <= a;
  } else {
    assert Minimum(a, b) == b;
    assert 0 <= b;
  }
}
// </vc-helpers>

// <vc-spec>
method Diagonal(matrix: seq<seq<real>>, offset: int := 0) returns (result: seq<real>)
  // Precondition: Matrix must be rectangular (all rows have same length)
  requires |matrix| > 0 ==> (forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|)
  // Precondition: Matrix dimensions must accommodate the offset for meaningful results
  requires |matrix| > 0 ==> 
    if offset >= 0 then offset <= |matrix[0]| 
    else -offset <= |matrix|
  // Postcondition: Result size matches diagonal size calculation
  ensures |matrix| == 0 ==> |result| == 0
  ensures |matrix| > 0 ==> 
    |result| == (if offset >= 0 
                 then Minimum(|matrix|, |matrix[0]| - offset)
                 else Minimum(|matrix[0]|, |matrix| + offset))
  // Postcondition: Each element comes from correct diagonal position
  ensures |matrix| > 0 ==> forall i :: 0 <= i < |result| ==>
    (if offset >= 0 
     then result[i] == matrix[i][i + offset]
     else result[i] == matrix[i + (-offset)][i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): removed 'call' keyword for lemmas and added non-negativity assertions */
  if |matrix| == 0 {
    result := [];
  } else {
    var rows := |matrix|;
    var cols := |matrix[0]|;
    if offset >= 0 {
      assert offset <= cols;
      var diagLen := Minimum(rows, cols - offset);
      MinNonNeg(rows, cols - offset);
      assert 0 <= diagLen;
      assert diagLen == Minimum(rows, cols - offset);
      MinLeLeft(rows, cols - offset);
      MinLeRight(rows, cols - offset);
      assert diagLen <= rows;
      assert diagLen <= cols - offset;
      var k := 0;
      result := [];
      while k < diagLen
        invariant 0 <= k <= diagLen
        invariant |result| == k
        invariant forall i :: 0 <= i < |result| ==> result[i] == matrix[i][i + offset]
        decreases diagLen - k
      {
        assert k < rows;
        assert k + offset < cols;
        assert 0 <= k;
        assert 0 <= k + offset;
        assert |matrix[k]| == cols;
        var elem := matrix[k][k + offset];
        result := result + [elem];
        k := k + 1;
      }
    } else {
      assert -offset <= rows;
      var diagLen := Minimum(cols, rows + offset);
      MinNonNeg(cols, rows + offset);
      assert 0 <= diagLen;
      assert diagLen == Minimum(cols, rows + offset);
      MinLeLeft(cols, rows + offset);
      MinLeRight(cols, rows + offset);
      assert diagLen <= cols;
      assert diagLen <= rows + offset;
      var k := 0;
      result := [];
      while k < diagLen
        invariant 0 <= k <= diagLen
        invariant |result| == k
        invariant forall i :: 0 <= i < |result| ==> result[i] == matrix[i + (-offset)][i]
        decreases diagLen - k
      {
        assert k < cols;
        assert k + (-offset) < rows;
        assert 0 <= k;
        assert 0 <= k + (-offset);
        assert |matrix[k + (-offset)]| == cols;
        var elem := matrix[k + (-offset)][k];
        result := result + [elem];
        k := k + 1;
      }
    }
  }
}
// </vc-code>
