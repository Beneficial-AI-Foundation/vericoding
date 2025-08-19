//https://numpy.org/doc/stable/reference/generated/numpy.where.html

//Return elements chosen from x or y depending on condition.

method where(condition: int->bool, arr: array<int>, change: int->int) returns (ret: array<int>)
    requires arr.Length > 0;
    ensures ret.Length == arr.Length
    ensures forall i :: 0 <= i < arr.Length ==> if condition(arr[i]) then ret[i] == change(arr[i]) else ret[i] == arr[i]
{}