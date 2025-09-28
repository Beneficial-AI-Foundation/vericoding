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
/* helper modified by LLM (iteration 4): relaxed precondition by moving it to ensures clause */
lemma SpacedValueInRange(start: real, stop: real, total: nat)
    requires total > 0
    ensures (start < stop) ==> (forall index: nat :: index < total ==> start <= SpacedValue(start, stop, index, total) < stop)
{
    if start < stop {
        forall index: nat | index < total
            ensures start <= SpacedValue(start, stop, index, total) < stop
        {
            var val := SpacedValue(start, stop, index, total);
            
            // Proof for lower bound: val >= start
            assert (index as real) >= 0.0;
            assert (total as real) > 0.0;
            assert stop - start > 0.0;
            assert (index as real) * (stop - start) / (total as real) >= 0.0;
            assert val >= start;

            // Proof for upper bound: val < stop
            calc {
                val;
            == // by definition of SpacedValue
                start + (index as real) * (stop - start) / (total as real);
            == // real arithmetic, since total != 0
                start + ((index as real) / (total as real)) * (stop - start);
            <  // since index < total, (index as real) < (total as real), and (stop-start) > 0.0
                start + 1.0 * (stop - start);
            == // real arithmetic
                stop;
            }
        }
    }
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
  /* code modified by LLM (iteration 4): added nat casts to fix subset constraint errors */
  SpacedValueInRange(start_r, stop_r, rows);
  SpacedValueInRange(start_c, stop_c, cols);

  row_coords := seq(rows, i => seq(cols, _ => SpacedValue(start_r, stop_r, i as nat, rows)));
  
  var col_values_row := seq(cols, j => SpacedValue(start_c, stop_c, j as nat, cols));
  col_coords := seq(rows, _ => col_values_row);
}
// </vc-code>
