datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//IMPL

// 5.
method maxArrayReverse(arr : array<int>) returns (max: int)
 requires arr.Length > 0
 ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
 ensures exists x::0 <= x < arr.Length && arr[x] == max
{
    max := arr[0];
    var maxIndex := 0;
    var i := 1;
    
    while i < arr.Length
        invariant 1 <= i <= arr.Length
        invariant 0 <= maxIndex < arr.Length
        invariant max == arr[maxIndex]
        invariant forall j: int :: 0 <= j < i ==> arr[j] <= max
    {
        if arr[i] > max {
            max := arr[i];
            maxIndex := i;
        }
        i := i + 1;
    }
}