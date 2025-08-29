//SPEC
method reshape(arr: array<int>, shape: array<int>) returns (ret: array2<int>)
    requires shape.Length == 2;
    requires forall i :: 0 <= i < 2 ==> shape[i] > 0 || shape[i] == - 1 
    requires !(shape[0] == -1 && shape[1] == -1);
    requires if shape[0] > 0 && shape[1] > 0 then shape[0] * shape[1] == arr.Length else if shape[0] == -1 then arr.Length % shape[1] == 0 else arr.Length % shape [0] == 0;
    ensures if shape[0] > 0 then ret.Length0 == shape[0] else ret.Length0 == arr.Length/shape[1];
    ensures if shape[1] > 0 then ret.Length1 == shape[1] else ret.Length1 == arr.Length/shape[0];
    ensures forall i :: 0 <= i < arr.Length ==> i/ret.Length1 < ret.Length0 && ret[i/ret.Length1, i%ret.Length1] == arr[i];
{} 