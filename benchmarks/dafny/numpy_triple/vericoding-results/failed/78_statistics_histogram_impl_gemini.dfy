// <vc-preamble>
datatype HistogramResult = HistogramResult(counts: seq<nat>, bin_edges: seq<real>)

predicate InRange(x: real, min_val: real, max_val: real)
{
    min_val <= x <= max_val
}

predicate MonotonicallyIncreasing(edges: seq<real>)
{
    forall i, j :: 0 <= i < j < |edges| ==> edges[i] < edges[j]
}

predicate UniformBinWidths(edges: seq<real>, n_bins: nat, min_val: real, max_val: real)
    requires |edges| == n_bins + 1
    requires n_bins > 0
{
    var expected_width := (max_val - min_val) / (n_bins as real);
    forall i :: 0 <= i < n_bins ==> edges[i+1] - edges[i] == expected_width
}

function CountInBin(data: seq<real>, left_edge: real, right_edge: real): nat
{
    |set i | 0 <= i < |data| && left_edge <= data[i] < right_edge|
}

function CountInBinCorrect(data: seq<real>, bin_index: nat, edges: seq<real>): nat
    requires bin_index < |edges| - 1
    requires |edges| >= 2
{
    var left_edge := edges[bin_index];
    var right_edge := edges[bin_index + 1];
    if bin_index == |edges| - 2 then
        // Rightmost bin: inclusive on both ends
        |set i | 0 <= i < |data| && left_edge <= data[i] <= right_edge|
    else
        // Other bins: left-inclusive, right-exclusive
        |set i | 0 <= i < |data| && left_edge <= data[i] < right_edge|
}

function CountInRange(data: seq<real>, min_val: real, max_val: real): nat
{
    |set i | 0 <= i < |data| && InRange(data[i], min_val, max_val)|
}

function SumCounts(counts: seq<nat>): nat
{
    if |counts| == 0 then 0
    else counts[0] + SumCounts(counts[1..])
}
// </vc-preamble>

// <vc-helpers>
method CountInBinMethod(data: seq<real>, bin_index: nat, edges: seq<real>) returns (count: nat)
    requires bin_index < |edges| - 1
    requires |edges| >= 2
    ensures count == CountInBinCorrect(data, bin_index, edges)
{
    var left_edge := edges[bin_index];
    var right_edge := edges[bin_index + 1];
    count := 0;
    var i := 0;
    while i < |data|
        invariant 0 <= i <= |data|
        invariant count == (
            if bin_index == |edges| - 2 then
                |set j | 0 <= j < i && left_edge <= data[j] <= right_edge|
            else
                |set j | 0 <= j < i && left_edge <= data[j] < right_edge|
        )
    {
        if bin_index == |edges| - 2 {
            if left_edge <= data[i] <= right_edge {
                count := count + 1;
            }
        } else {
            if left_edge <= data[i] < right_edge {
                count := count + 1;
            }
        }
        i := i + 1;
    }
}

lemma SumCountsIsCountInRange(data: seq<real>, counts: seq<nat>, edges: seq<real>)
    requires |counts| == |edges| - 1 && |counts| > 0
    requires MonotonicallyIncreasing(edges)
    requires forall i :: 0 <= i < |counts| ==> counts[i] == CountInBinCorrect(data, i, edges)
    ensures SumCounts(counts) == CountInRange(data, edges[0], edges[|edges|-1])
    decreases |counts|
{
    if |counts| > 1 {
        var rest_counts := counts[1..];
        var rest_edges := edges[1..];
        assert forall i :: 0 <= i < |rest_counts| :: rest_counts[i] == CountInBinCorrect(data, i, rest_edges);
        SumCountsIsCountInRange(data, rest_counts, rest_edges);

        var s1 := set i | 0 <= i < |data| && edges[0] <= data[i] < edges[1];
        var s2 := set i | 0 <= i < |data| && edges[1] <= data[i] <= edges[|edges|-1];
        assert s1 * s2 == {};
        var s_total := set i | 0 <= i < |data| && edges[0] <= data[i] <= edges[|edges|-1];
        assert s1 + s2 == s_total;
    }
}
// </vc-helpers>

// <vc-spec>
method Histogram(data: seq<real>, min_val: real, max_val: real, n_bins: nat) returns (result: HistogramResult)
    requires n_bins > 0
    requires min_val < max_val
    ensures |result.counts| == n_bins
    ensures |result.bin_edges| == n_bins + 1
    // Bin edges are monotonically increasing
    ensures MonotonicallyIncreasing(result.bin_edges)
    // Boundary conditions: first edge is min_val, last edge is max_val
    ensures result.bin_edges[0] == min_val
    ensures result.bin_edges[n_bins] == max_val
    // Uniform binning: all bin widths are equal
    ensures UniformBinWidths(result.bin_edges, n_bins, min_val, max_val)
    // Each bin count matches the actual number of data points in that bin
    ensures forall i :: 0 <= i < n_bins ==>
        result.counts[i] == CountInBinCorrect(data, i, result.bin_edges)
    // Conservation: total count equals number of data points in range
    ensures SumCounts(result.counts) == CountInRange(data, min_val, max_val)
// </vc-spec>
// <vc-code>
{
    var width := (max_val - min_val) / (n_bins as real);
    var temp_edges := new real[n_bins + 1];
    var i : nat := 0;
    while i <= n_bins
        invariant 0 <= i <= n_bins + 1
        invariant forall j :: 0 <= j < i ==> temp_edges[j] == min_val + (j as real) * width
    {
        temp_edges[i] := min_val + (i as real) * width;
        i := i + 1;
    }
    var edges_seq := temp_edges[..];

    assert UniformBinWidths(edges_seq, n_bins, min_val, max_val);

    var temp_counts := new nat[n_bins];
    var k : nat := 0;
    while k < n_bins
        invariant 0 <= k <= n_bins
        invariant forall j :: 0 <= j < k ==> temp_counts[j] == CountInBinCorrect(data, j, edges_seq)
    {
        temp_counts[k] := CountInBinMethod(data, k, edges_seq);
        k := k + 1;
    }
    var counts_seq := temp_counts[..];
    assert forall j :: 0 <= j < n_bins ==> counts_seq[j] == CountInBinCorrect(data, j, edges_seq);

    SumCountsIsCountInRange(data, counts_seq, edges_seq);

    result := HistogramResult(counts_seq, edges_seq);
}
// </vc-code>
