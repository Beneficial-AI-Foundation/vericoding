//ATOM

// 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)


// SPEC

// 5.
method maxArrayReverse(arr : array<int>) returns (max: int)
 requires arr.Length > 0
 ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
 ensures exists x::0 <= x < arr.Length && arr[x] == max
{
}
