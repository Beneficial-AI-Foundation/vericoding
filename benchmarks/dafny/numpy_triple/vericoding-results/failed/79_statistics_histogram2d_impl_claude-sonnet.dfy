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
/* helper modified by LLM (iteration 5): fixed CreateEdges to properly handle equal min/max case while maintaining monotonicity postcondition */
function FindMin(s: seq<real>): real
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] <= FindMin(s[1..]) then s[0]
    else FindMin(s[1..])
}

function FindMax(s: seq<real>): real
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= FindMax(s[1..]) then s[0]
    else FindMax(s[1..])
}

function CreateEdges(min_val: real, max_val: real, bins: nat): seq<real>
    requires bins > 0
    requires min_val < max_val
    ensures |CreateEdges(min_val, max_val, bins)| == bins + 1
    ensures CreateEdges(min_val, max_val, bins)[0] == min_val
    ensures CreateEdges(min_val, max_val, bins)[bins] == max_val
    ensures forall i :: 0 <= i < bins ==> CreateEdges(min_val, max_val, bins)[i] < CreateEdges(min_val, max_val, bins)[i + 1]
{
    var step := (max_val - min_val) / (bins as real);
    seq(bins + 1, i => if i == bins then max_val else min_val + (i as real) * step)
}

function InitializeHistogram(bins: nat): seq<seq<nat>>
    ensures |InitializeHistogram(bins)| == bins
    ensures forall i :: 0 <= i < |InitializeHistogram(bins)| ==> |InitializeHistogram(bins)[i]| == bins
    ensures forall i, j :: 0 <= i < |InitializeHistogram(bins)| && 0 <= j < |InitializeHistogram(bins)[i]| ==> InitializeHistogram(bins)[i][j] == 0
{
    seq(bins, i => seq(bins, j => 0))
}

function FindBinIndex(val: real, edges: seq<real>, bins: nat): nat
    requires |edges| == bins + 1
    requires bins > 0
    requires edges[0] <= val <= edges[bins]
    requires forall i :: 0 <= i < bins ==> edges[i] < edges[i + 1]
    ensures 0 <= FindBinIndex(val, edges, bins) < bins
{
    FindBinIndexHelper(val, edges, 0, bins)
}

function FindBinIndexHelper(val: real, edges: seq<real>, start: nat, bins: nat): nat
    requires |edges| == bins + 1
    requires 0 <= start < bins
    requires edges[0] <= val <= edges[bins]
    requires forall i :: 0 <= i < bins ==> edges[i] < edges[i + 1]
    ensures start <= FindBinIndexHelper(val, edges, start, bins) < bins
    decreases bins - start
{
    if start == bins - 1 then start
    else if val < edges[start + 1] then start
    else FindBinIndexHelper(val, edges, start + 1, bins)
}

function UpdateHistogram(hist: seq<seq<nat>>, i: nat, j: nat): seq<seq<nat>>
    requires 0 <= i < |hist|
    requires 0 <= j < |hist[i]|
    ensures |UpdateHistogram(hist, i, j)| == |hist|
    ensures forall k :: 0 <= k < |UpdateHistogram(hist, i, j)| ==> |UpdateHistogram(hist, i, j)[k]| == |hist[k]|
    ensures UpdateHistogram(hist, i, j)[i][j] == hist[i][j] + 1
    ensures forall k, l :: (0 <= k < |hist| && 0 <= l < |hist[k]| && (k != i || l != j)) ==> UpdateHistogram(hist, i, j)[k][l] == hist[k][l]
    ensures SumHistogram(UpdateHistogram(hist, i, j)) == SumHistogram(hist) + 1
{
    hist[i := hist[i][j := hist[i][j] + 1]]
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
    /* code modified by LLM (iteration 5): ensure min < max by using epsilon adjustment and fix loop invariant */
    var x_min := FindMin(x);
    var x_max := FindMax(x);
    var y_min := FindMin(y);
    var y_max := FindMax(y);
    
    // Ensure min < max by adjusting with epsilon
    var epsilon := 0.0000000001;
    var x_min_adj := x_min - epsilon;
    var x_max_adj := x_max + epsilon;
    var y_min_adj := y_min - epsilon;
    var y_max_adj := y_max + epsilon;
    
    var x_edges := CreateEdges(x_min_adj, x_max_adj, bins);
    var y_edges := CreateEdges(y_min_adj, y_max_adj, bins);
    
    var histogram := InitializeHistogram(bins);
    
    var k := 0;
    while k < |x|
        invariant 0 <= k <= |x|
        invariant |histogram| == bins
        invariant forall i :: 0 <= i < |histogram| ==> |histogram[i]| == bins
        invariant forall i, j :: 0 <= i < |histogram| && 0 <= j < |histogram[i]| ==> histogram[i][j] <= k
        invariant SumHistogram(histogram) == k
        invariant forall l :: 0 <= l < k ==> x_min_adj <= x[l] <= x_max_adj
        invariant forall l :: 0 <= l < k ==> y_min_adj <= y[l] <= y_max_adj
    {
        var x_bin := FindBinIndex(x[k], x_edges, bins);
        var y_bin := FindBinIndex(y[k], y_edges, bins);
        histogram := UpdateHistogram(histogram, x_bin, y_bin);
        k := k + 1;
    }
    
    result := Histogram2DResult(histogram, x_edges, y_edges);
}
// </vc-code>
