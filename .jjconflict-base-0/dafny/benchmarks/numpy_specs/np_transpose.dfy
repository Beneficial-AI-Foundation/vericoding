//SPEC
method transpose<T>(arr: array2<T>) returns (ret: array2<T>)
    ensures ret.Length0 == arr.Length1
    ensures ret.Length1 == arr.Length0
    ensures forall i, j :: 0 <= i < arr.Length0 && 0 <= j < arr.Length1 ==> 
        ret[j, i] == arr[i, j]
{}