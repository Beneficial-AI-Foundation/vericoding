//https://numpy.org/doc/stable/reference/generated/numpy.tril.html

//Lower triangle of an array.Return a copy of an array with elements above the k-th diagonal zeroed. For arrays with ndim exceeding 2, tril will apply to the final two axes.

//IMPL tril
method tril (arr : array2<int>, k : int) returns (ret: array2<int>)
    requires -arr.Length0 + 1 < k < arr.Length1 - 1;
    ensures ret.Length0 == arr.Length0 && ret.Length1 == arr.Length1; 
    ensures forall i, j:: 0 <= i < arr.Length0 && 0 <= j < arr.Length1 ==> if j- i > k then ret[i , j] == 0 else ret[i, j] == arr[i, j];
{
    ret := new int[arr.Length0, arr.Length1];
    
    var i := 0;
    while i < arr.Length0
        invariant 0 <= i <= arr.Length0
        invariant ret.Length0 == arr.Length0 && ret.Length1 == arr.Length1
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < arr.Length1 ==> 
            if jj - ii > k then ret[ii, jj] == 0 else ret[ii, jj] == arr[ii, jj]
    {
        var j := 0;
        while j < arr.Length1
            invariant 0 <= j <= arr.Length1
            invariant ret.Length0 == arr.Length0 && ret.Length1 == arr.Length1
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < arr.Length1 ==> 
                if jj - ii > k then ret[ii, jj] == 0 else ret[ii, jj] == arr[ii, jj]
            invariant forall jj :: 0 <= jj < j ==> 
                if jj - i > k then ret[i, jj] == 0 else ret[i, jj] == arr[i, jj]
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