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
method FindMinMax(s: seq<real>) returns (min_val: real, max_val: real)
    requires |s| > 0
    ensures min_val <= max_val
    ensures forall i :: 0 <= i < |s| ==> min_val <= s[i] <= max_val
    ensures exists i :: 0 <= i < |s| && s[i] == min_val
    ensures exists i :: 0 <= i < |s| && s[i] == max_val
{
    min_val := s[0];
    max_val := s[0];
    var i := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> min_val <= s[j] <= max_val
        invariant exists j :: 0 <= j < i && s[j] == min_val
        invariant exists j :: 0 <= j < i && s[j] == max_val
    {
        if s[i] < min_val {
            min_val := s[i];
        } else if s[i] > max_val {
            max_val := s[i];
        }
        i := i + 1;
    }
}

/* helper modified by LLM (iteration 2): fixed function signature to name the return value */
function GenerateEdges(min_val: real, max_val: real, bins: nat): (result: seq<real>)
    requires bins > 0
    requires min_val < max_val
    ensures |result| == bins + 1
    ensures result[0] == min_val
    ensures result[bins] == max_val
    ensures forall i :: 0 <= i < |result| - 1 ==> result[i] < result[i+1]
{
    var step := (max_val - min_val) / (bins as real);
    seq(bins + 1, i => min_val + (i as real) * step)
}

method FindBinIndex(val: real, edges: seq<real>, bins: nat) returns (idx: nat)
    requires bins > 0
    requires |edges| == bins + 1
    requires forall i :: 0 <= i < |edges| - 1 ==> edges[i] < edges[i + 1]
    requires edges[0] <= val <= edges[|edges| - 1]
    ensures 0 <= idx < bins
    ensures idx < bins - 1 ==> edges[idx] <= val < edges[idx+1]
    ensures idx == bins - 1 ==> edges[idx] <= val <= edges[idx+1]
{
    if val == edges[bins] {
        idx := bins - 1;
        return;
    }

    var i := 0;
    while i < bins - 1
        invariant 0 <= i < bins
        invariant forall j :: 0 <= j < i ==> val >= edges[j+1]
    {
        if val < edges[i+1] {
            idx := i;
            return;
        }
        i := i + 1;
    }
    idx := bins - 1;
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
{
    /* code modified by LLM (iteration 2): resubmitting code to check for verification errors after compilation fix */
    var x_min_val, x_max_val := FindMinMax(x);
    if x_min_val == x_max_val {
        x_min_val := x_min_val - 0.5;
        x_max_val := x_max_val + 0.5;
    }

    var y_min_val, y_max_val := FindMinMax(y);
    if y_min_val == y_max_val {
        y_min_val := y_min_val - 0.5;
        y_max_val := y_max_val + 0.5;
    }

    var x_edges := GenerateEdges(x_min_val, x_max_val, bins);
    var y_edges := GenerateEdges(y_min_val, y_max_val, bins);

    var hist := seq(bins, i => seq(bins, j => 0));

    var k: nat := 0;
    while k < |x|
        invariant 0 <= k <= |x|
        invariant |hist| == bins && forall i :: 0 <= i < bins ==> |hist[i]| == bins
        invariant SumHistogram(hist) == k
        invariant forall i, j :: 0 <= i < bins && 0 <= j < bins ==> 
            hist[i][j] == CountPointsInBin(x[..k], y[..k], i, j, x_edges, y_edges, bins)
    {
        var x_val := x[k];
        var y_val := y[k];
        
        var i_idx := FindBinIndex(x_val, x_edges, bins);
        var j_idx := FindBinIndex(y_val, y_edges, bins);

        var old_row := hist[i_idx];
        var updated_row := old_row[j_idx := old_row[j_idx] + 1];
        hist := hist[i_idx := updated_row];
        
        k := k + 1;
    }

    result := Histogram2DResult(hist, x_edges, y_edges);
}
// </vc-code>
