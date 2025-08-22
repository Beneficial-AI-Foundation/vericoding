//IMPL
method where(condition: int->bool, arr: array<int>, change: int->int) returns (ret: array<int>)
    requires arr.Length > 0
    ensures ret.Length == arr.Length
    ensures forall i :: 0 <= i < arr.Length ==> if condition(arr[i]) then ret[i] == change(arr[i]) else ret[i] == arr[i]
{
    ret := new int[arr.Length];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < i ==> if condition(arr[j]) then ret[j] == change(arr[j]) else ret[j] == arr[j]
    {
        if condition(arr[i]) {
            ret[i] := change(arr[i]);
        } else {
            ret[i] := arr[i];
        }
        i := i + 1;
    }
}