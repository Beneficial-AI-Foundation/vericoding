datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//IMPL 

// 3.
method maxArray(arr : array<int>) returns (max: int)
 requires arr.Length > 0
 ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
 ensures exists x::0 <= x < arr.Length && arr[x] == max
{
    max := arr[0];
    var maxIndex := 0;
    
    for i := 1 to arr.Length
        invariant 0 <= maxIndex < arr.Length
        invariant max == arr[maxIndex]
        invariant forall j: int :: 0 <= j < i ==> arr[j] <= max
        invariant exists x :: 0 <= x < i && arr[x] == max
    {
        if arr[i] > max {
            max := arr[i];
            maxIndex := i;
        }
    }
}