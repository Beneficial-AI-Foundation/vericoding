//IMPL copyArr
method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
 requires 0 <= l < r <= a.Length 
 ensures ret[..] == a[l..r]
{
    ret := new int[r - l];
    var i := 0;
    while i < r - l
        invariant 0 <= i <= r - l
        invariant ret[..i] == a[l..l+i]
    {
        ret[i] := a[l + i];
        i := i + 1;
    }
}