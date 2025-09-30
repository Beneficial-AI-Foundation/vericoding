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
/* helper modified by LLM (iteration 2): prove bounds of Minimum */
lemma Minimum_le(a: int, b: int)
  ensures Minimum(a, b) <= a && Minimum(a, b) <= b
{
  if a <= b {
    assert Minimum(a, b) == a;
    assert a <= a;
    assert a <= b;
  } else {
    assert Minimum(a, b) == b;
    assert b <= a;
    assert b <= b;
  }
}

/* helper modified by LLM (iteration 2): Minimum equals one of its inputs */
lemma Minimum_is_one_of_inputs(a: int, b: int)
  ensures Minimum(a, b) == a || Minimum(a, b) == b
{
  if a <= b {
    assert Minimum(a, b) == a;
  } else {
    assert Minimum(a, b) == b;
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
  /* code modified by LLM (iteration 2): build diagonal sequence with loop and invariants */
  if |matrix| == 0 {
    result := [];
    return;
  }
  var rows := |matrix|;
  var cols := |matrix[0]|;
  var n := if offset >= 0 then Minimum(rows, cols - offset) else Minimum(cols, rows + offset);
  result := [];
  var i := 0;
  if offset >= 0 {
    while i < n
      invariant 0 <= i <= n
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> result[j] == matrix[j][j + offset]
    {
      result := result + [matrix[i][i + offset]];
      i := i + 1;
    }
  } else {
    var off := -offset;
    while i < n
      invariant 0 <= i <= n
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> result[j] == matrix[j + off][j]
    {
      result := result + [matrix[i + off][i]];
      i := i + 1;
    }
  }
}

// </vc-code>
