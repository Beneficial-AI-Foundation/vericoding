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
/* helper modified by LLM (iteration 5): ensure positive width yields increasing edges */
lemma WidthPositiveImpliesIncrease(xmin: real, xmax: real, bins: nat)
  requires bins > 0
  requires xmax > xmin
  ensures forall i :: 0 <= i < bins ==> xmin + (i as real) * ((xmax - xmin) / (bins as real)) < xmin + ((i + 1) as real) * ((xmax - xmin) / (bins as real))
{
  var width := (xmax - xmin) / (bins as real);
  assert width > 0;
  forall i | 0 <= i < bins {
    assert xmin + (i as real) * width < xmin + ((i + 1) as real) * width;
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
/* code modified by LLM (iteration 5): compute histogram bins and edges; fixed casts and sequence construction */
{
  var xmin := x[0];
  var xmax := x[0];
  var idx := 1;
  while idx < |x|
    decreases |x| - idx
    invariant 1 <= idx <= |x|
    invariant forall t :: 0 <= t < idx ==> xmin <= x[t] && x[t] <= xmax
  {
    if x[idx] < xmin { xmin := x[idx]; }
    if x[idx] > xmax { xmax := x[idx]; }
    idx := idx + 1;
  }
  if xmax <= xmin { xmax := xmin + 1.0; }

  var ymin := y[0];
  var ymax := y[0];
  idx := 1;
  while idx < |y|
    decreases |y| - idx
    invariant 1 <= idx <= |y|
    invariant forall t :: 0 <= t < idx ==> ymin <= y[t] && y[t] <= ymax
  {
    if y[idx] < ymin { ymin := y[idx]; }
    if y[idx] > ymax { ymax := y[idx]; }
    idx := idx + 1;
  }
  if ymax <= ymin { ymax := ymin + 1.0; }

  var width_x := (xmax - xmin) / (bins as real);
  var width_y := (ymax - ymin) / (bins as real);

  var xarr := new real[bins + 1];
  var i := 0;
  while i <= bins
    decreases (bins + 1) - i
    invariant 0 <= i <= bins + 1
    invariant forall t :: 0 <= t < i ==> xarr[t] == xmin + (t as real) * width_x
  {
    xarr[i] := xmin + (i as real) * width_x;
    i := i + 1;
  }

  var yarr := new real[bins + 1];
  i := 0;
  while i <= bins
    decreases (bins + 1) - i
    invariant 0 <= i <= bins + 1
    invariant forall t :: 0 <= t < i ==> yarr[t] == ymin + (t as real) * width_y
  {
    yarr[i] := ymin + (i as real) * width_y;
    i := i + 1;
  }

  var edgesX := xarr[..];
  var edgesY := yarr[..];

  var harr := new nat[bins][];
  i := 0;
  while i < bins
    decreases bins - i
    invariant 0 <= i <= bins
    invariant forall t :: 0 <= t < i ==> harr[t].Length == bins
  {
    harr[i] := new nat[bins];
    i := i + 1;
  }

  var k := 0;
  while k < |x|
    decreases |x| - k
    invariant 0 <= k <= |x|
    invariant forall ii, jj :: 0 <= ii < bins && 0 <= jj < bins ==>
                harr[ii][jj] == |set t | 0 <= t < k && BinContains(x[t], y[t], ii, jj, edgesX, edgesY, bins)|
  {
    var xi := x[k];
    var yi := y[k];

    var di := (xi - xmin) / width_x;
    var dj := (yi - ymin) / width_y;
    var idi := (int)di;
    var idj := (int)dj;
    var iidx := if idi < 0 then 0 else if idi >= bins then bins - 1 else idi;
    var jidx := if idj < 0 then 0 else if idj >= bins then bins - 1 else idj;

    harr[iidx][jidx] := harr[iidx][jidx] + 1;

    k := k + 1;
  }

  var histarr := new seq<nat>[bins];
  i := 0;
  while i < bins
    decreases bins - i
    invariant 0 <= i <= bins
    invariant forall t :: 0 <= t < i ==> histarr[t] == harr[t][..]
  {
    histarr[i] := harr[i][..];
    i := i + 1;
  }

  result.x_edges := edgesX;
  result.y_edges := edgesY;
  result.histogram := histarr[..];
}

// </vc-code>
