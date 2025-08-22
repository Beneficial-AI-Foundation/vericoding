//SPEC
method ravel<T>(arr: array2<T>) returns (ret: array<T>)
    ensures ret.Length == arr.Length0 * arr.Length1
    ensures forall i, j :: 0 <= i < arr.Length0 && 0 <= j < arr.Length1 ==> ret[i * arr.Length1 + j] == arr[i, j]
{}