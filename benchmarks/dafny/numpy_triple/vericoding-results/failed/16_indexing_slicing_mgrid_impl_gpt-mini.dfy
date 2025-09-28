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
/* helper modified by LLM (iteration 5): row sequence builder */
function RowForIndexAux(value: real, k: nat): seq<real>
  decreases k
  ensures |result| == k
  ensures forall idx :: 0 <= idx < |result| ==> result[idx] == value
{
  if k == 0 then [] else RowForIndexAux(value, k - 1) + [value]
}

/* helper modified by LLM (iteration 5): row wrapper producing a row of repeated spaced values */
function RowForIndex(start: real, stop: real, i: nat, rows: nat, cols: nat): seq<real>
  requires cols > 0 && rows > 0 && i < rows
  decreases cols
  ensures |result| == cols
  ensures forall j :: 0 <= j < |result| ==> result[j] == SpacedValue(start, stop, i, rows)
{
  RowForIndexAux(SpacedValue(start, stop, i, rows), cols)
}

/* helper modified by LLM (iteration 5): column sequence builder helper */
function ColRowAux(start: real, stop: real, total: nat, k: nat): seq<real>
  requires total > 0 && k <= total
  decreases k
  ensures |result| == k
  ensures forall idx :: 0 <= idx < |result| ==> result[idx] == SpacedValue(start, stop, idx, total)
{
  if k == 0 then [] else ColRowAux(start, stop, total, k - 1) + [SpacedValue(start, stop, k - 1, total)]
}

/* helper modified by LLM (iteration 5): column wrapper producing the template column row */
function ColRow(start: real, stop: real, total: nat): seq<real>
  requires total > 0
  decreases total
  ensures |result| == total
  ensures forall j :: 0 <= j < |result| ==> result[j] == SpacedValue(start, stop, j, total)
{
  ColRowAux(start, stop, total, total)
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
  /* code modified by LLM (iteration 5): construct matrices using helpers */
  var rc_build: seq<seq<real>> := [];
  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant |rc_build| == i
    invariant forall p :: 0 <= p < |rc_build| ==> |rc_build[p]| == cols
    invariant forall p, j :: 0 <= p < |rc_build| && 0 <= j < cols ==> rc_build[p][j] == SpacedValue(start_r, stop_r, p, rows)
  {
    rc_build := rc_build + [RowForIndex(start_r, stop_r, i, rows, cols)];
    i := i + 1;
  }
  row_coords := rc_build;

  var col_template := ColRow(start_c, stop_c, cols);
  var cc_build: seq<seq<real>> := [];
  var k := 0;
  while k < rows
    invariant 0 <= k <= rows
    invariant |cc_build| == k
    invariant forall p :: 0 <= p < |cc_build| ==> |cc_build[p]| == cols
    invariant forall p, j :: 0 <= p < |cc_build| && 0 <= j < cols ==> cc_build[p][j] == col_template[j]
  {
    cc_build := cc_build + [col_template];
    k := k + 1;
  }
  col_coords := cc_build;
}

// </vc-code>
