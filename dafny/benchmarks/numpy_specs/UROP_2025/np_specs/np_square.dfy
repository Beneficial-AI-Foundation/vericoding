//https://numpy.org/doc/stable/reference/generated/numpy.square.html

//Return the element-wise square of the input.

method square (arr: array<int>) returns (ret: array<int>)
    ensures ret.Length == arr.Length;
    ensures forall i :: 0 <= i < arr.Length ==> ret[i] == arr[i] * arr[i];
{}