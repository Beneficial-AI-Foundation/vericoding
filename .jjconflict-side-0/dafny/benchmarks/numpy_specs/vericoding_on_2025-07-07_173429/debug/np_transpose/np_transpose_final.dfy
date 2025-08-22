//IMPL
method transpose<T>(arr: array2<T>) returns (ret: array2<T>)
    ensures ret.Length0 == arr.Length1
    ensures ret.Length1 == arr.Length0
    ensures forall i, j :: 0 <= i < arr.Length0 && 0 <= j < arr.Length1 ==> 
        ret[j, i] == arr[i, j]
{
    ret := new T[arr.Length1, arr.Length0];
    
    var i := 0;
    while i < arr.Length0
        invariant 0 <= i <= arr.Length0
        invariant forall i', j :: 0 <= i' < i && 0 <= j < arr.Length1 ==> 
            ret[j, i'] == arr[i', j]
    {
        var j := 0;
        while j < arr.Length1
            invariant 0 <= j <= arr.Length1
            invariant forall i', j' :: 0 <= i' < i && 0 <= j' < arr.Length1 ==> 
                ret[j', i'] == arr[i', j']
            invariant forall j' :: 0 <= j' < j ==> ret[j', i] == arr[i, j']
        {
            ret[j, i] := arr[i, j];
            j := j + 1;
        }
        i := i + 1;
    }
}