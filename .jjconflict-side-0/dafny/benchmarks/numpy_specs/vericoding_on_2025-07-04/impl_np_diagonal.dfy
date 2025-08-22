//IMPL
method diagonal (arr: array2<int>, k: int) returns (ret: array<int>)
    requires arr.Length0 == arr.Length1
    requires -arr.Length0 < k < arr.Length0
    ensures if k > 0 then ret.Length == arr.Length0 - k else ret.Length == arr.Length0 + k
    ensures forall i :: 0 <= i < ret.Length==> (if k >= 0 then ret[i] == arr[i, i + k] else ret[i] == arr[i - k, i])
{
    var n := arr.Length0;
    var len := if k > 0 then n - k else n + k;
    ret := new int[len];
    
    var i := 0;
    while i < len
        invariant 0 <= i <= len
        invariant forall j :: 0 <= j < i ==> (if k >= 0 then ret[j] == arr[j, j + k] else ret[j] == arr[j - k, j])
    {
        if k >= 0 {
            ret[i] := arr[i, i + k];
        } else {
            ret[i] := arr[i - k, i];
        }
        i := i + 1;
    }
}