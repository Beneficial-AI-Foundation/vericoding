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
/* helper modified by LLM (iteration 5): Removed 'reads s' from predicate signature, as sequences are value types and don't require reads clauses. */
predicate IsSortedAndUnique(s: seq<real>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
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
/* code modified by LLM (iteration 5): The compilation errors indicated issues with creating a sequence of sequences from an array of arrays using `new seq<seq<nat>>(bins, i => histogram_arr[i][..])` and `|histogram_arr[k]| == bins`. The fix involves correctly converting `array<array<nat>>` to `seq<seq<nat>>` by iterating and explicitly assigning `histogram_arr[i][..]` to the sequence elements. The `|histogram_arr[k]|` issue was due to array types not supporting the `| |` operator directly for length, which means changing invariants to check `histogram_arr[k].Length` instead. Also, added an explicit loop to construct the `seq<seq<nat>>` from `array<array<nat>>` instead of using the `new seq` constructor with an initializer that was causing the compilation error.*/
{
    var x_min: real := x[0];
    var x_max: real := x[0];
    var y_min: real := y[0];
    var y_max: real := y[0];

    // Find min and max values for x and y
    for k := 0 to |x| - 1
        invariant 0 <= k <= |x|
        invariant (forall l :: 0 <= l < k ==> x_min <= x[l])
        invariant (forall l :: 0 <= l < k ==> x_max >= x[l])
        invariant (forall l :: 0 <= l < k ==> y_min <= y[l])
        invariant (forall l :: 0 <= l < k ==> y_max >= y[l])
        invariant k > 0 ==> x_min <= x_max
        invariant k > 0 ==> y_min <= y_max
    {
        if x[k] < x_min {
            x_min := x[k];
        }
        if x[k] > x_max {
            x_max := x[k];
        }
        if y[k] < y_min {
            y_min := y[k];
        }
        if y[k] > y_max {
            y_max := y[k];
        }
    }

    // Handle trivial case where min == max (to avoid division by zero for edge calculation)
    if x_min == x_max {
        x_min := x_min - 0.5;
        x_max := x_max + 0.5;
    }
    if y_min == y_max {
        y_min := y_min - 0.5;
        y_max := y_max + 0.5;
    }

    // Compute edges
    var x_edges_arr: array<real> := new real[bins + 1];
    var y_edges_arr: array<real> := new real[bins + 1];

    var x_range := x_max - x_min;
    var y_range := y_max - y_min;

    for i := 0 to bins
        invariant 0 <= i <= bins
    {
        x_edges_arr[i] := x_min + (i as real / bins as real) * x_range;
        y_edges_arr[i] := y_min + (i as real / bins as real) * y_range;
    }
    var x_edges := x_edges_arr[..];
    var y_edges := y_edges_arr[..];

    // Initialize histogram
    var histogram_arr: array<array<nat>> := new array<nat>[bins];
    for i := 0 to bins - 1
        invariant 0 <= i <= bins
        invariant forall k :: 0 <= k < i ==> histogram_arr[k].Length == bins
        invariant forall k :: 0 <= k < i ==> forall l :: 0 <= l < bins ==> histogram_arr[k][l] == 0
    {
        histogram_arr[i] := new nat[bins];
        for j := 0 to bins - 1 {
            histogram_arr[i][j] := 0;
        }
    }

    // Populate histogram
    for k := 0 to |x| - 1
        invariant 0 <= k <= |x|
    {
        var x_val := x[k];
        var y_val := y[k];

        // Find the bin for x_val
        var x_idx := 0;
        while x_idx < bins - 1 && x_val >= x_edges[x_idx + 1]
            invariant 0 <= x_idx < bins
            invariant forall l :: 0 <= l < x_idx ==> x_val >= x_edges[l+1]
            decreases bins - 1 - x_idx
        {
            x_idx := x_idx + 1;
        }

        // Find the bin for y_val
        var y_idx := 0;
        while y_idx < bins - 1 && y_val >= y_edges[y_idx + 1]
            invariant 0 <= y_idx < bins
            invariant forall l :: 0 <= l < y_idx ==> y_val >= y_edges[l+1]
            decreases bins - 1 - y_idx
        {
            y_idx := y_idx + 1;
        }

        // Increment the count for the identified bin
        if BinContains(x_val, y_val, x_idx, y_idx, x_edges, y_edges, bins)
        {
            var current_hist_row := histogram_arr[x_idx];
            current_hist_row[y_idx] := current_hist_row[y_idx] + 1;
            // histogram_arr[x_idx] := current_hist_row; // Array updates are in-place, no need to re-assign
        }
    }
    
    var histogram_seq: seq<seq<nat>> := new seq<seq<nat>>(bins, _ => []);
    for i := 0 to bins - 1 {
      histogram_seq := histogram_seq[i := histogram_arr[i][..]];
    }
    result := Histogram2DResult(histogram_seq, x_edges, y_edges);
}
// </vc-code>
