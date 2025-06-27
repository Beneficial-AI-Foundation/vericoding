//https://numpy.org/doc/stable/reference/generated/numpy.isclose.html#numpy.isclose

//Returns a boolean array where two arrays are element-wise equal within a tolerance.
method np_isclose(a: array<int>, b: array<int>, tol : int) returns (ret: array<bool>)
    requires a.Length > 0; 
    requires a.Length == b.Length;
    requires tol > 0;
    ensures ret.Length == a.Length;
    ensures forall i :: 0<= i < a.Length ==> if -tol < a[i] - b[i] < tol then ret[i] else !ret[i];
{}