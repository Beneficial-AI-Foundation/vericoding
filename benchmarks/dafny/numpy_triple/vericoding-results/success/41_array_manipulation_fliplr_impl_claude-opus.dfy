// <vc-preamble>
/*
 * Specification for numpy.fliplr: Reverse the order of elements along axis 1 (left/right).
 * This function flips a 2D matrix horizontally, reversing the column order in each row
 * while preserving the row order and the elements within each row.
 */

// Predicate to check if a 2D matrix is well-formed (rectangular)
predicate IsWellFormedMatrix<T>(m: seq<seq<T>>)
{
    |m| > 0 && 
    (forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|) &&
    |m[0]| > 0
}

// Predicate to check if two rows contain the same multiset of elements
predicate SameElements<T(==)>(row1: seq<T>, row2: seq<T>)
{
    multiset(row1) == multiset(row2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed ReverseRowElements lemma proof */
function ReverseRow(row: seq<real>): seq<real>
{
  if |row| == 0 then []
  else ReverseRow(row[1..]) + [row[0]]
}

lemma ReverseRowLength(row: seq<real>)
  ensures |ReverseRow(row)| == |row|
{
  if |row| == 0 {
  } else {
    ReverseRowLength(row[1..]);
  }
}

lemma ReverseRowElements(row: seq<real>)
  ensures multiset(ReverseRow(row)) == multiset(row)
{
  if |row| == 0 {
    assert ReverseRow(row) == [];
    assert multiset(ReverseRow(row)) == multiset([]);
    assert multiset(row) == multiset([]);
  } else {
    ReverseRowElements(row[1..]);
    var tail := row[1..];
    var revTail := ReverseRow(tail);
    assert multiset(revTail) == multiset(tail);
    assert ReverseRow(row) == revTail + [row[0]];
    assert multiset(ReverseRow(row)) == multiset(revTail + [row[0]]);
    assert multiset(revTail + [row[0]]) == multiset(revTail) + multiset{row[0]};
    assert multiset(revTail) + multiset{row[0]} == multiset(tail) + multiset{row[0]};
    assert row == [row[0]] + tail;
    assert multiset(row) == multiset([row[0]] + tail);
    assert multiset([row[0]] + tail) == multiset{row[0]} + multiset(tail);
    assert multiset(tail) + multiset{row[0]} == multiset{row[0]} + multiset(tail);
  }
}

lemma ReverseRowCorrect(row: seq<real>)
  ensures |ReverseRow(row)| == |row|
  ensures forall j :: 0 <= j < |row| ==> ReverseRow(row)[j] == row[|row|-1-j]
{
  ReverseRowLength(row);
  if |row| == 0 {
  } else if |row| == 1 {
  } else {
    ReverseRowCorrect(row[1..]);
    var rev := ReverseRow(row[1..]);
    assert |rev| == |row[1..]|;
    assert ReverseRow(row) == rev + [row[0]];
    forall j | 0 <= j < |row|
      ensures ReverseRow(row)[j] == row[|row|-1-j]
    {
      if j < |rev| {
        assert ReverseRow(row)[j] == rev[j];
        assert rev[j] == row[1..][|row[1..]|-1-j];
        assert row[1..][|row[1..]|-1-j] == row[|row|-1-j];
      } else {
        assert j == |rev|;
        assert j == |row| - 1;
        assert ReverseRow(row)[j] == row[0];
        assert row[0] == row[|row|-1-j];
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method FlipLR(m: seq<seq<real>>) returns (result: seq<seq<real>>)
    requires IsWellFormedMatrix(m)
    requires |m| >= 1 && |m[0]| >= 1  // At least 2D matrix
    ensures IsWellFormedMatrix(result)
    ensures |result| == |m|
    ensures |result[0]| == |m[0]|
    // Element mapping: result[i][j] == m[i][cols-1-j]
    ensures forall i :: 0 <= i < |result| ==>
        forall j :: 0 <= j < |result[i]| ==>
            result[i][j] == m[i][|m[i]|-1-j]
    // Row preservation: each row contains the same elements
    ensures forall i :: 0 <= i < |result| ==>
        SameElements(result[i], m[i])
    // Dimensions are preserved
    ensures forall i :: 0 <= i < |result| ==>
        |result[i]| == |m[i]|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implementation unchanged, relies on fixed lemma */
{
  var rows := |m|;
  var cols := |m[0]|;
  result := [];
  
  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == cols
    invariant forall k :: 0 <= k < i ==> result[k] == ReverseRow(m[k])
    invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < cols ==> result[k][j] == m[k][cols-1-j]
    invariant forall k :: 0 <= k < i ==> SameElements(result[k], m[k])
  {
    var reversed := ReverseRow(m[i]);
    ReverseRowLength(m[i]);
    ReverseRowCorrect(m[i]);
    ReverseRowElements(m[i]);
    result := result + [reversed];
    i := i + 1;
  }
}
// </vc-code>
