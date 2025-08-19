//ATOM

// 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)


//IMPL 

// 3.
method maxArray(arr : array<int>) returns (max: int)
 requires arr.Length > 0
 ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
 ensures exists x::0 <= x < arr.Length && arr[x] == max
{
    max := arr[0];
    var i := 1;
    
    while i < arr.Length
        invariant 1 <= i <= arr.Length
        invariant forall j :: 0 <= j < i ==> arr[j] <= max
        invariant exists k :: 0 <= k < i && arr[k] == max
    {
        if arr[i] > max {
            max := arr[i];
        }
        i := i + 1;
    }
}