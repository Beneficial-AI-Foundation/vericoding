- `requires arr.Length >= 0` - the array length is non-negative (always true)
- `ensures num >= 0` - the result must be non-negative
- `ensures arr[0] == 0.0 ==> nonzero(arr[1..]) == num - 1` - this describes the relationship but notes recursion is not allowed

The second postcondition seems to be describing the recursive relationship for specification purposes, but since recursion is not allowed, I need to implement this iteratively.

The method should count the number of non-zero elements in the array.

//IMPL
method nonzero(arr: array<real>) returns (num: int)
    requires arr.Length >= 0; 
    ensures num >= 0; 
    ensures arr[0] == 0.0 ==> nonzero(arr[1..]) == num - 1 //recursion is not allowed i
{
    num := 0;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant num >= 0
    {
        if arr[i] != 0.0 {
            num := num + 1;
        }
        i := i + 1;
    }
}