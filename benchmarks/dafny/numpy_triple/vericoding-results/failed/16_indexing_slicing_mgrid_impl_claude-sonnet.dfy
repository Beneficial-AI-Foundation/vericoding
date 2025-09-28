// <vc-preamble>
// Type alias for 2D array representation
type Matrix = seq<seq<real>>

// Helper predicate to check if a matrix has the specified dimensions
predicate ValidMatrix(m: Matrix, rows: nat, cols: nat)
{
    |m| == rows &&
    forall i :: 0 <= i < rows ==> |m[i]| == cols
}

// Helper function to compute evenly spaced coordinate values
function SpacedValue(start: real, stop: real, index: nat, total: nat): real
    requires total > 0
{
    start + (index as real) * (stop - start) / (total as real)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added precondition for valid range bounds to handle strict inequality postconditions */
lemma SpacedValueBounds(start: real, stop: real, index: nat, total: nat)
    requires total > 0
    requires index < total
    requires start < stop
    ensures start <= SpacedValue(start, stop, index, total) < stop
{
    var value := SpacedValue(start, stop, index, total);
    assert value == start + (index as real) * (stop - start) / (total as real);
    assert 0.0 <= (index as real) < (total as real);
    assert 0.0 <= (index as real) / (total as real) < 1.0;
}

lemma SpacedValueAtZero(start: real, stop: real, total: nat)
    requires total > 0
    ensures SpacedValue(start, stop, 0, total) == start
{
    assert SpacedValue(start, stop, 0, total) == start + 0.0 * (stop - start) / (total as real);
}
// </vc-helpers>

// <vc-spec>
method mgrid(rows: nat, cols: nat, start_r: real, stop_r: real, start_c: real, stop_c: real) 
    returns (row_coords: Matrix, col_coords: Matrix)
    requires rows > 0 && cols > 0
    ensures ValidMatrix(row_coords, rows, cols)
    ensures ValidMatrix(col_coords, rows, cols)
    // Row coordinates: same value across each row
    ensures (forall i, j, k :: 0 <= i < rows && 0 <= j < cols && 0 <= k < cols ==> row_coords[i][j] == row_coords[i][k])
    // Column coordinates: same value down each column
    ensures (forall j, i, k :: 0 <= j < cols && 0 <= i < rows && 0 <= k < rows ==> col_coords[i][j] == col_coords[k][j])
    // Row coordinates are evenly spaced
    ensures (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> row_coords[i][j] == SpacedValue(start_r, stop_r, i, rows))
    // Column coordinates are evenly spaced  
    ensures (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> col_coords[i][j] == SpacedValue(start_c, stop_c, j, cols))
    // Boundary conditions: first coordinates match start points
    ensures forall j :: 0 <= j < cols ==> row_coords[0][j] == start_r
    ensures forall i :: 0 <= i < rows ==> col_coords[i][0] == start_c
    // Grid coverage: coordinates are within their respective ranges (exclusive of stop)
    ensures (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> start_r <= row_coords[i][j] < stop_r)
    ensures (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> start_c <= col_coords[i][j] < stop_c)
    // Mathematical property: coordinates form a complete dense grid
    ensures (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> row_coords[i][j] == start_r + (i as real) * (stop_r - start_r) / (rows as real))
    ensures (forall i, j :: 0 <= i < rows && 0 <= j < cols ==> col_coords[i][j] == start_c + (j as real) * (stop_c - start_c) / (cols as real))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): removed assume statements and added conditional bounds checking */
  row_coords := seq(rows, i requires 0 <= i < rows => seq(cols, j requires 0 <= j < cols => SpacedValue(start_r, stop_r, i, rows)));
  col_coords := seq(rows, i requires 0 <= i < rows => seq(cols, j requires 0 <= j < cols => SpacedValue(start_c, stop_c, j, cols)));
  
  if start_r < stop_r {
    forall i, j | 0 <= i < rows && 0 <= j < cols
      ensures start_r <= row_coords[i][j] < stop_r
    {
      SpacedValueBounds(start_r, stop_r, i, rows);
    }
  }
  
  if start_c < stop_c {
    forall i, j | 0 <= i < rows && 0 <= j < cols
      ensures start_c <= col_coords[i][j] < stop_c
    {
      SpacedValueBounds(start_c, stop_c, j, cols);
    }
  }
}
// </vc-code>
