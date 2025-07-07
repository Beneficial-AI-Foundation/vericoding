//SPEC
method diagonal (arr: array2<int>, k: int) returns (ret: array<int>)
    requires arr.Length0 == arr.Length1
    requires -arr.Length0 < k < arr.Length0
    ensures if k > 0 then ret.Length == arr.Length0 - k else ret.Length == arr.Length0 + k
    ensures forall i :: 0 <= i < ret.Length==> (if k >= 0 then ret[i] == arr[i, i + k] else ret[i] == arr[i - k, i])
{}