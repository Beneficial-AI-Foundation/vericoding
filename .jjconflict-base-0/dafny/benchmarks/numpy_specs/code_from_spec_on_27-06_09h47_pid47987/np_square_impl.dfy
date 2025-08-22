//https://numpy.org/doc/stable/reference/generated/numpy.square.html

//Return the element-wise square of the input.

//IMPL square
method square (arr: array<int>) returns (ret: array<int>)
    ensures ret.Length == arr.Length;
    ensures forall i :: 0 <= i < arr.Length ==> ret[i] == arr[i] * arr[i];
{
    ret := new int[arr.Length];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant ret.Length == arr.Length
        invariant forall j :: 0 <= j < i ==> ret[j] == arr[j] * arr[j]
    {
        ret[i] := arr[i] * arr[i];
        i := i + 1;
    }
}