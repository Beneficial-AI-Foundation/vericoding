// https://numpy.org/doc/stable/reference/generated/numpy.arange.html#numpy.arange

//Return an array copy of the given object.
method copy (arr: array<int>) returns (ret: array<int>)
    ensures ret.Length == arr.Length;
    ensures forall i :: 0 <= i < arr.Length ==> ret[i] == arr[i];
{}