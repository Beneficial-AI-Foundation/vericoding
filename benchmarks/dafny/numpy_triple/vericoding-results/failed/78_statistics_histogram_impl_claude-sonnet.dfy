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
/* helper modified by LLM (iteration 5): fixed BinPartitionLemma by removing union syntax error and fixing partition logic */
function CreateBinEdges(min_val: real, max_val: real, n_bins: nat): seq<real>
    requires n_bins > 0
    requires min_val < max_val
    ensures |CreateBinEdges(min_val, max_val, n_bins)| == n_bins + 1
    ensures CreateBinEdges(min_val, max_val, n_bins)[0] == min_val
    ensures CreateBinEdges(min_val, max_val, n_bins)[n_bins] == max_val
    ensures MonotonicallyIncreasing(CreateBinEdges(min_val, max_val, n_bins))
    ensures UniformBinWidths(CreateBinEdges(min_val, max_val, n_bins), n_bins, min_val, max_val)
{
    var width := (max_val - min_val) / (n_bins as real);
    seq(n_bins + 1, i => min_val + (i as real) * width)
}

function CreateCounts(data: seq<real>, edges: seq<real>): seq<nat>
    requires |edges| >= 2
    ensures |CreateCounts(data, edges)| == |edges| - 1
    ensures forall i :: 0 <= i < |edges| - 1 ==>
        CreateCounts(data, edges)[i] == CountInBinCorrect(data, i, edges)
{
    seq(|edges| - 1, i requires 0 <= i < |edges| - 1 => CountInBinCorrect(data, i, edges))
}

lemma SumCountsCorrectness(data: seq<real>, edges: seq<real>, min_val: real, max_val: real)
    requires |edges| >= 2
    requires edges[0] == min_val
    requires edges[|edges| - 1] == max_val
    requires MonotonicallyIncreasing(edges)
    ensures SumCounts(CreateCounts(data, edges)) == CountInRange(data, min_val, max_val)
{
    var counts := CreateCounts(data, edges);
    BinPartitionLemma(data, edges, min_val, max_val);
}

lemma BinPartitionLemma(data: seq<real>, edges: seq<real>, min_val: real, max_val: real)
    requires |edges| >= 2
    requires edges[0] == min_val
    requires edges[|edges| - 1] == max_val
    requires MonotonicallyIncreasing(edges)
    ensures SumCounts(CreateCounts(data, edges)) == CountInRange(data, min_val, max_val)
{
    var counts := CreateCounts(data, edges);
    var in_range_set := set i | 0 <= i < |data| && InRange(data[i], min_val, max_val);
    
    var bin_sets := seq(|edges| - 1, bin => 
        set i | 0 <= i < |data| && 
            ((bin == |edges| - 2 && edges[bin] <= data[i] <= edges[bin+1]) ||
             (bin < |edges| - 2 && edges[bin] <= data[i] < edges[bin+1])));
    
    assert forall i :: 0 <= i < |counts| ==> counts[i] == |bin_sets[i]|;
    assert forall bin1, bin2 :: 0 <= bin1 < bin2 < |bin_sets| ==> bin_sets[bin1] * bin_sets[bin2] == {};
    
    var all_bins_union := (set bin, i | 0 <= bin < |bin_sets| && i in bin_sets[bin] :: i);
    assert all_bins_union == in_range_set;
    
    SumCountsPartition(counts, bin_sets, in_range_set);
}

lemma SumCountsPartition(counts: seq<nat>, bin_sets: seq<set<nat>>, total_set: set<nat>)
    requires |counts| == |bin_sets|
    requires forall i :: 0 <= i < |counts| ==> counts[i] == |bin_sets[i]|
    requires forall i, j :: 0 <= i < j < |bin_sets| ==> bin_sets[i] * bin_sets[j] == {}
    requires (set bin, i | 0 <= bin < |bin_sets| && i in bin_sets[bin] :: i) == total_set
    ensures SumCounts(counts) == |total_set|
{
    if |counts| == 0 {
        assert total_set == {};
    } else {
        var rest_union := (set bin, i | 0 <= bin < |bin_sets| - 1 && i in bin_sets[bin + 1] :: i);
        assert total_set == bin_sets[0] + rest_union;
        assert bin_sets[0] * rest_union == {};
        SumCountsPartition(counts[1..], bin_sets[1..], rest_union);
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
    /* code modified by LLM (iteration 5): simplified implementation without unnecessary variables */
    var bin_edges := CreateBinEdges(min_val, max_val, n_bins);
    var counts := CreateCounts(data, bin_edges);
    
    SumCountsCorrectness(data, bin_edges, min_val, max_val);
    
    result := HistogramResult(counts, bin_edges);
}
// </vc-code>
