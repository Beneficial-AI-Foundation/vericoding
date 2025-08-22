//IMPL

method histogram (data: array<real>, bins: array<real>) returns (hist: array<int>) 
    requires bins.Length >= 2 
    requires forall i :: 1 <= i < bins.Length ==> bins[i] > bins[i-1]
    ensures hist.Length == bins.Length - 1
{
    hist := new int[bins.Length - 1];
    
    // Initialize histogram to zeros
    var i := 0;
    while i < hist.Length
        invariant 0 <= i <= hist.Length
        invariant forall j :: 0 <= j < i ==> hist[j] == 0
    {
        hist[i] := 0;
        i := i + 1;
    }
    
    // Count data points in each bin
    var dataIndex := 0;
    while dataIndex < data.Length
        invariant 0 <= dataIndex <= data.Length
        invariant forall j :: 0 <= j < hist.Length ==> hist[j] >= 0
    {
        histogram_helper(data, bins, hist, dataIndex);
        dataIndex := dataIndex + 1;
    }
}

//IMPL

method histogram_helper(data: array<real>, bins: array<real>, hist: array<int>, index: int)
    requires bins.Length >= 2
    requires forall i :: 1 <= i < bins.Length ==> bins[i] > bins[i-1]
    requires 0 <= index < data.Length
    requires hist.Length == bins.Length - 1
    modifies hist
{
    var binIndex := 0;
    while binIndex < bins.Length - 1
        invariant 0 <= binIndex <= bins.Length - 1
    {
        /* code modified by LLM (iteration 1): simplified condition using precondition knowledge */
        if data[index] >= bins[binIndex] && data[index] < bins[binIndex + 1] {
            /* code modified by LLM (iteration 1): removed redundant bounds check since binIndex < bins.Length - 1 and hist.Length == bins.Length - 1 */
            hist[binIndex] := hist[binIndex] + 1;
            return;
        }
        binIndex := binIndex + 1;
    }
    
    /* code modified by LLM (iteration 1): handle case where data point is >= last bin boundary */
    if data[index] >= bins[bins.Length - 1] {
        hist[hist.Length - 1] := hist[hist.Length - 1] + 1;
    }
}