//https://numpy.org/doc/stable/reference/generated/numpy.tril.html

//Lower triangle of an array.Return a copy of an array with elements above the k-th diagonal zeroed. For arrays with ndim exceeding 2, tril will apply to the final two axes.

method tril (arr : array2<int>, k : int) returns (ret: array2<int>)
    requires -arr.Length0 + 1 < k < arr.Length1 - 1;
    ensures ret.Length0 == arr.Length0 && ret.Length1 == arr.Length1; 
    ensures forall i, j:: 0 <= i < arr.Length0 && 0 <= j < arr.Length1 ==> if j- i > k then ret[i , j] == 0 else ret[i, j] == arr[i, j];
{}