//https://numpy.org/doc/stable/reference/generated/numpy.reshape.html

//IMPL reshape
//reshapes
//one of the inputs can be negative one, in which case the other dimensions is inferred 
method reshape(arr: array<int>, shape: array<int>) returns (ret: array2<int>)
    requires shape.Length == 2;
    requires forall i :: 0 <= i < 2 ==> shape[i] > 0 || shape[i] == - 1 
    requires !(shape[0] == -1 && shape[1] == -1);
    requires if shape[0] > 0 && shape[1] > 0 then shape[0] * shape[1] == arr.Length else if shape[0] == -1 then arr.Length % shape[1] == 0 else arr.Length % shape [0] == 0;
    ensures if shape[0] > 0 then ret.Length0 == shape[0] else ret.Length0 == arr.Length/shape[1];
    ensures if shape[1] > 0 then ret.Length1 == shape[1] else ret.Length1 == arr.Length/shape[0];
    ensures forall i :: 0 <= i < arr.Length ==> i/ret.Length1 < ret.Length0 && ret[i/ret.Length1, i%ret.Length1] == arr[i];
{
    var dim0: int;
    var dim1: int;
    
    if shape[0] > 0 {
        dim0 := shape[0];
    } else {
        dim0 := arr.Length / shape[1];
    }
    
    if shape[1] > 0 {
        dim1 := shape[1];
    } else {
        dim1 := arr.Length / shape[0];
    }
    
    ret := new int[dim0, dim1];
    
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < i ==> j/ret.Length1 < ret.Length0 && ret[j/ret.Length1, j%ret.Length1] == arr[j]
    {
        var row := i / dim1;
        var col := i % dim1;
        ret[row, col] := arr[i];
        i := i + 1;
    }
}