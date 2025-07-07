//IMPL

method histogram (data: array<real>, bins: array<real>) returns (hist: array<int>) 
    requires bins.Length >= 2 
    requires forall i :: 1 <= i < bins.Length ==> bins[i] > bins[i-1]
    ensures hist.Length == bins.Length - 1
    ensures 0 <= data.Length
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
    requires forall j :: 0 <= j < hist.Length ==> hist[j] >= 0
    modifies hist
    ensures forall j :: 0 <= j < hist.Length ==> hist[j] >= 0
{
    var binIndex := 0;
    while binIndex < bins.Length - 1
        invariant 0 <= binIndex <= bins.Length - 1
    {
        /* code modified by LLM (iteration 1): fixed bin boundary logic and added proper bounds checking */
        if binIndex < bins.Length - 1 && data[index] >= bins[binIndex] && data[index] < bins[binIndex + 1] {
            hist[binIndex] := hist[binIndex] + 1;
            return;
        }
        binIndex := binIndex + 1;
    }
    
    /* code modified by LLM (iteration 1): handle edge case for data points at or above the last bin boundary */
    // Handle the case where data point is >= last bin boundary
    if data[index] >= bins[bins.Length - 1] {
        hist[hist.Length - 1] := hist[hist.Length - 1] + 1;
    }
}