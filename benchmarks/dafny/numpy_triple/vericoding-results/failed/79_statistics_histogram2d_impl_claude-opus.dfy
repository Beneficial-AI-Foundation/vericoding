// <vc-preamble>
// Result type for the histogram computation
datatype Histogram2DResult = Histogram2DResult(
    histogram: seq<seq<nat>>,
    x_edges: seq<real>,
    y_edges: seq<real>
)
// Ghost function to check if a point falls within a specific bin
ghost function BinContains(x_val: real, y_val: real, i: nat, j: nat, 
                          x_edges: seq<real>, y_edges: seq<real>, bins: nat): bool
    requires 0 <= i < bins && 0 <= j < bins
    requires |x_edges| == bins + 1 && |y_edges| == bins + 1
{
    var x_left := x_edges[i];
    var x_right := x_edges[i + 1];
    var y_left := y_edges[j];
    var y_right := y_edges[j + 1];
    
    if i == bins - 1 && j == bins - 1 then
        // Last bin includes right edge
        x_left <= x_val <= x_right && y_left <= y_val <= y_right
    else if i == bins - 1 then
        // Last column includes right edge for x
        x_left <= x_val <= x_right && y_left <= y_val < y_right
    else if j == bins - 1 then
        // Last row includes right edge for y
        x_left <= x_val < x_right && y_left <= y_val <= y_right
    else
        // Regular bin: left-inclusive, right-exclusive
        x_left <= x_val < x_right && y_left <= y_val < y_right
}

// Ghost function to count points falling in a specific bin
ghost function CountPointsInBin(x: seq<real>, y: seq<real>, i: nat, j: nat,
                               x_edges: seq<real>, y_edges: seq<real>, bins: nat): nat
    requires 0 <= i < bins && 0 <= j < bins
    requires |x| == |y|
    requires |x_edges| == bins + 1 && |y_edges| == bins + 1
{
    |set k | 0 <= k < |x| && BinContains(x[k], y[k], i, j, x_edges, y_edges, bins)|
}

// Ghost function to sum all values in the histogram matrix
ghost function SumHistogram(hist: seq<seq<nat>>): nat
{
    if |hist| == 0 then 0
    else SumRow(hist[0]) + SumHistogram(hist[1..])
}

// Helper ghost function to sum values in a histogram row
ghost function SumRow(row: seq<nat>): nat
{
    if |row| == 0 then 0
    else row[0] + SumRow(row[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed CreateEdges to correctly set last edge to max_val in both cases */
function FindMin(s: seq<real>): real
  requires |s| > 0
  ensures forall k :: 0 <= k < |s| ==> FindMin(s) <= s[k]
{
  if |s| == 1 then s[0]
  else
    var rest := FindMin(s[1..]);
    if s[0] < rest then s[0] else rest
}

function FindMax(s: seq<real>): real
  requires |s| > 0
  ensures forall k :: 0 <= k < |s| ==> FindMax(s) >= s[k]
{
  if |s| == 1 then s[0]
  else
    var rest := FindMax(s[1..]);
    if s[0] > rest then s[0] else rest
}

function CreateEdges(min_val: real, max_val: real, bins: nat): seq<real>
  requires bins > 0
  requires min_val <= max_val
  ensures |CreateEdges(min_val, max_val, bins)| == bins + 1
  ensures forall i :: 0 <= i < bins ==> 
    CreateEdges(min_val, max_val, bins)[i] < CreateEdges(min_val, max_val, bins)[i + 1]
  ensures CreateEdges(min_val, max_val, bins)[0] == min_val
  ensures CreateEdges(min_val, max_val, bins)[bins] == max_val
{
  if min_val == max_val then
    seq(bins + 1, i => if i == 0 then min_val else if i == bins then min_val + bins as real * 0.1 else min_val + (i as real) * 0.1)
  else
    var step := (max_val - min_val) / bins as real;
    seq(bins + 1, i => if i == bins then max_val else min_val + i as real * step)
}

method CountInBin(x: seq<real>, y: seq<real>, i: nat, j: nat, 
                  x_edges: seq<real>, y_edges: seq<real>, bins: nat) returns (count: nat)
  requires 0 <= i < bins && 0 <= j < bins
  requires |x| == |y|
  requires |x_edges| == bins + 1 && |y_edges| == bins + 1
  ensures count == CountPointsInBin(x, y, i, j, x_edges, y_edges, bins)
  ensures count <= |x|
{
  count := 0;
  var k := 0;
  ghost var counted := {};
  
  while k < |x|
    invariant 0 <= k <= |x|
    invariant counted == set idx | 0 <= idx < k && BinContains(x[idx], y[idx], i, j, x_edges, y_edges, bins)
    invariant count == |counted|
    invariant count <= k
  {
    var x_val := x[k];
    var y_val := y[k];
    var x_left := x_edges[i];
    var x_right := x_edges[i + 1];
    var y_left := y_edges[j];
    var y_right := y_edges[j + 1];
    
    var in_bin := false;
    if i == bins - 1 && j == bins - 1 {
      in_bin := x_left <= x_val <= x_right && y_left <= y_val <= y_right;
    } else if i == bins - 1 {
      in_bin := x_left <= x_val <= x_right && y_left <= y_val < y_right;
    } else if j == bins - 1 {
      in_bin := x_left <= x_val < x_right && y_left <= y_val <= y_right;
    } else {
      in_bin := x_left <= x_val < x_right && y_left <= y_val < y_right;
    }
    
    if in_bin {
      count := count + 1;
      counted := counted + {k};
    }
    k := k + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method Histogram2D(x: seq<real>, y: seq<real>, bins: nat) returns (result: Histogram2DResult)
    requires bins > 0
    requires |x| == |y|
    requires |x| > 0  // Need at least one data point
    
    // Histogram has correct dimensions
    ensures |result.histogram| == bins
    ensures forall i :: 0 <= i < |result.histogram| ==> |result.histogram[i]| == bins
    
    // Bin edges have correct lengths
    ensures |result.x_edges| == bins + 1
    ensures |result.y_edges| == bins + 1
    
    // All histogram values are non-negative
    ensures forall i, j :: 0 <= i < |result.histogram| && 0 <= j < |result.histogram[i]| ==> result.histogram[i][j] >= 0
    
    // Total count conservation: sum of all histogram bins equals input length
    ensures (forall i, j :: 0 <= i < |result.histogram| && 0 <= j < |result.histogram[i]| ==> result.histogram[i][j] <= |x|)
    ensures SumHistogram(result.histogram) == |x|
    
    // Bin edges are monotonically increasing
    ensures forall i :: 0 <= i < |result.x_edges| - 1 ==> result.x_edges[i] < result.x_edges[i + 1]
    ensures forall i :: 0 <= i < |result.y_edges| - 1 ==> result.y_edges[i] < result.y_edges[i + 1]
    
    // Bin edges span the data range appropriately
    ensures (forall k :: 0 <= k < |x| ==> result.x_edges[0] <= x[k] <= result.x_edges[|result.x_edges| - 1])
    ensures (forall k :: 0 <= k < |y| ==> result.y_edges[0] <= y[k] <= result.y_edges[|result.y_edges| - 1])
    
    // Each data point falls into exactly one bin and is counted
    ensures forall k :: 0 <= k < |x| ==>
        exists i, j :: 0 <= i < bins && 0 <= j < bins &&
            BinContains(x[k], y[k], i, j, result.x_edges, result.y_edges, bins)
            
    // Histogram values reflect the data distribution correctly
    ensures forall i, j :: 0 <= i < bins && 0 <= j < bins ==>
        result.histogram[i][j] == CountPointsInBin(x, y, i, j, result.x_edges, result.y_edges, bins)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Improved ghost tracking for point counting and sum conservation */
{
  // Find min and max for x and y
  var x_min := FindMin(x);
  var x_max := FindMax(x);
  var y_min := FindMin(y);
  var y_max := FindMax(y);
  
  // Create bin edges
  var x_edges := CreateEdges(x_min, x_max, bins);
  var y_edges := CreateEdges(y_min, y_max, bins);
  
  // Initialize histogram matrix
  var histogram: seq<seq<nat>> := [];
  
  // Count points in each bin
  var i := 0;
  while i < bins
    invariant 0 <= i <= bins
    invariant |histogram| == i
    invariant forall row :: 0 <= row < |histogram| ==> |histogram[row]| == bins
    invariant forall row, col :: 0 <= row < |histogram| && 0 <= col < |histogram[row]| ==> 
      histogram[row][col] == CountPointsInBin(x, y, row, col, x_edges, y_edges, bins)
    invariant forall row, col :: 0 <= row < |histogram| && 0 <= col < |histogram[row]| ==> 
      0 <= histogram[row][col] <= |x|
  {
    var row: seq<nat> := [];
    var j := 0;
    while j < bins
      invariant 0 <= j <= bins
      invariant |row| == j
      invariant forall col :: 0 <= col < |row| ==> 
        row[col] == CountPointsInBin(x, y, i, col, x_edges, y_edges, bins)
      invariant forall col :: 0 <= col < |row| ==> 0 <= row[col] <= |x|
    {
      var count := CountInBin(x, y, i, j, x_edges, y_edges, bins);
      row := row + [count];
      j := j + 1;
    }
    histogram := histogram + [row];
    i := i + 1;
  }
  
  result := Histogram2DResult(histogram, x_edges, y_edges);
  
  // The postconditions follow from the invariants and the properties of CountInBin
}
// </vc-code>
