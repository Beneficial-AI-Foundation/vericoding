//https://numpy.org/doc/stable/reference/generated/numpy.argmax.html

//Returns the index of the maximum value along an axis.
//returns index of first occurences
method argmax (arr: array<real>) returns (ret: nat)
    requires arr.Length > 0;
    ensures ret < arr.Length;
    ensures forall i :: 0 <= i < ret ==> arr[ret] > arr[i];
    ensures forall i :: ret < i < arr.Length ==> arr[ret] >= arr[i]; 
{
    ret := 0;
    var k := 1;
    
    while k < arr.Length
        invariant 0 <= ret < arr.Length
        invariant 1 <= k <= arr.Length
        invariant forall i :: 0 <= i < ret ==> arr[ret] > arr[i]
        invariant forall i :: ret < i < k ==> arr[ret] >= arr[i]
    {
        if arr[k] > arr[ret] {
            ret := k;
        }
        k := k + 1;
    }
}