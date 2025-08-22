//SPEC
method nonzero(arr: array<real>) returns (num: int)
    requires arr.Length >= 0; 
    ensures num >= 0; 
    ensures arr[0] == 0.0 ==> nonzero(arr[1..]) == num - 1 //recursion is not allowed i
{}