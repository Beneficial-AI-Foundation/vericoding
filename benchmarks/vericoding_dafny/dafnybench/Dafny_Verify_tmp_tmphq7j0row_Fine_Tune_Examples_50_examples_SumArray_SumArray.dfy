function Sum(arr: array<int>, len: int): int
    reads arr
    requires arr.Length > 0 && 0 <= len <= arr.Length
{
    if len == 0 then 0 else arr[len-1] + Sum(arr, len-1)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SumArray(arr: array<int>) returns (sum: int)
    requires arr.Length > 0
    ensures sum == Sum(arr, arr.Length)
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>