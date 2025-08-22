//IMPL
method tril (arr : array2<int>, k : int) returns (ret: array2<int>)
    requires -arr.Length0 + 1 < k < arr.Length1 - 1
    ensures ret.Length0 == arr.Length0 && ret.Length1 == arr.Length1
    ensures forall i, j:: 0 <= i < arr.Length0 && 0 <= j < arr.Length1 ==> if j- i > k then ret[i , j] == 0 else ret[i, j] == arr[i, j]
{
    ret := new int[arr.Length0, arr.Length1];
    
    var i := 0;
    while i < arr.Length0
        invariant 0 <= i <= arr.Length0
        invariant ret.Length0 == arr.Length0 && ret.Length1 == arr.Length1
        invariant forall i', j':: 0 <= i' < i && 0 <= j' < arr.Length1 ==> if j' - i' > k then ret[i', j'] == 0 else ret[i', j'] == arr[i', j']
    {
        var j := 0;
        while j < arr.Length1
            invariant 0 <= j <= arr.Length1
            invariant ret.Length0 == arr.Length0 && ret.Length1 == arr.Length1
            invariant forall i', j':: 0 <= i' < i && 0 <= j' < arr.Length1 ==> if j' - i' > k then ret[i', j'] == 0 else ret[i', j'] == arr[i', j']
            invariant forall j':: 0 <= j' < j ==> if j' - i > k then ret[i, j'] == 0 else ret[i, j'] == arr[i, j']
        {
            if j - i > k {
                ret[i, j] := 0;
            } else {
                ret[i, j] := arr[i, j];
            }
            j := j + 1;
        }
        i := i + 1;
    }
}