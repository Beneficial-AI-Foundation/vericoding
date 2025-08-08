//IMPL
method argmax (arr: array<real>) returns (ret: nat)
    requires arr.Length > 0
    ensures ret < arr.Length
    ensures forall i :: 0 <= i < ret ==> arr[ret] > arr[i]
    ensures forall i :: ret < i < arr.Length ==> arr[ret] >= arr[i] 
{
    ret := 0;
    var j := 1;
    
    while j < arr.Length
        invariant 0 <= ret < arr.Length
        invariant 1 <= j <= arr.Length
        invariant forall i :: 0 <= i < ret ==> arr[ret] > arr[i]
        invariant forall i :: ret < i < j ==> arr[ret] >= arr[i]
    {
        if arr[j] > arr[ret] {
            ret := j;
        }
        j := j + 1;
    }
}