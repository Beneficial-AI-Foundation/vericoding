/*
{
  "name": "numpy.arange",
  "category": "Numerical ranges",
  "description": "Return evenly spaced values within a given interval",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.arange.html",
  "doc": "\nReturn evenly spaced values within a given interval.\n\nParameters\n----------\nstart : integer or real, optional\n    Start of interval. The interval includes this value. The default start value is 0.\nstop : integer or real\n    End of interval. The interval does not include this value, except in some cases where \n    step is not an integer and floating point round-off affects the length of out.\nstep : integer or real, optional\n    Spacing between values. For any output out, this is the distance between two adjacent \n    values, out[i+1] - out[i]. The default step size is 1.\ndtype : dtype, optional\n    The type of the output array. If dtype is not given, infer the data type from the \n    other input arguments.\ndevice : str, optional\n    Device on which to place the created array.\nlike : array_like, optional\n    Reference object to allow the creation of arrays which are not NumPy arrays.\n\nReturns\n-------\narange : ndarray\n    Array of evenly spaced values.\n\nExamples\n--------\n>>> np.arange(3)\narray([0, 1, 2])\n>>> np.arange(3.0)\narray([ 0.,  1.,  2.])\n>>> np.arange(3,7)\narray([3, 4, 5, 6])\n>>> np.arange(3,7,2)\narray([3, 5])\n\nNotes\n-----\nWhen using a non-integer step, such as 0.1, it is often better to use numpy.linspace.\n",
  "code": "# numpy.arange is implemented in C as part of the multiarray module\n# Python signature:\n@array_function_dispatch(_arange_dispatcher)\ndef arange(start=None, stop=None, step=None, dtype=None, *, device=None, like=None):\n    \"\"\"\n    Return evenly spaced values within a given interval.\n    \"\"\"\n    # Implementation is in C - multiarray.arange\n    # Handles various input formats: arange(stop), arange(start, stop), arange(start, stop, step)\n    pass",
  "signature": "numpy.arange([start, ]stop, [step, ]dtype=None, *, device=None, like=None)"
}
*/

// Return evenly spaced values within a given interval [start, stop) with given step
method arange(start: real, stop: real, step: real, n: nat) returns (result: array<real>)
    requires step != 0.0
    requires n == 0 ==> (step > 0.0 && start >= stop) || (step < 0.0 && start <= stop)
    requires n > 0 ==> 
        if step > 0.0 then 
            start < stop && n == ((stop - start) / step).Floor
        else 
            start > stop && n == ((start - stop) / (-step)).Floor
    ensures result.Length == n
    // Specification: arange generates evenly spaced values from start to stop (exclusive) with given step.
    // Each element at index i has value start + i * step, and all values are within bounds
    ensures n == 0 ==> 
        (step > 0.0 && start >= stop) || (step < 0.0 && start <= stop)
    ensures n > 0 ==> 
        forall i :: 0 <= i < n ==> result[i] == start + (i as real) * step
    ensures n > 0 && step > 0.0 ==> 
        start < stop && (forall i :: 0 <= i < n ==> result[i] < stop)
    ensures n > 0 && step < 0.0 ==> 
        start > stop && (forall i :: 0 <= i < n ==> result[i] > stop)
{
    result := new real[n];
    
    if n == 0 {
        // Empty array case - conditions already ensured by precondition
        return;
    }
    
    // Fill the array with evenly spaced values
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> result[j] == start + (j as real) * step
    {
        result[i] := start + (i as real) * step;
        i := i + 1;
    }
}

// Helper function to calculate the required array size given start, stop, and step
function calculateArraySize(start: real, stop: real, step: real): nat
    requires step != 0.0
{
    if step > 0.0 then
        if start >= stop then 0
        else 
            var size := ((stop - start) / step).Floor;
            if size >= 0 then size as nat else 0
    else
        if start <= stop then 0
        else
            var size := ((start - stop) / (-step)).Floor;
            if size >= 0 then size as nat else 0
}

// Convenient wrapper that automatically calculates the array size
method arangeAuto(start: real, stop: real, step: real) returns (result: array<real>)
    requires step != 0.0
    ensures result.Length == calculateArraySize(start, stop, step)
    ensures result.Length == 0 ==> 
        (step > 0.0 && start >= stop) || (step < 0.0 && start <= stop)
    ensures result.Length > 0 ==> 
        forall i :: 0 <= i < result.Length ==> result[i] == start + (i as real) * step
{
    var n := calculateArraySize(start, stop, step);
    
    if n == 0 {
        result := new real[0];
        return;
    }
    
    result := new real[n];
    
    // Fill the array with evenly spaced values
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> result[j] == start + (j as real) * step
    {
        result[i] := start + (i as real) * step;
        i := i + 1;
    }
}
