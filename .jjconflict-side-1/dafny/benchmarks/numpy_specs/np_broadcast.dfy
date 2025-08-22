//SPEC
method broadcast (a: array<int>, shape: array<int>) returns (ret: array2<int>)
    requires shape.Length == 2 
    requires shape[0] == a.Length || shape[1] == a.Length
    ensures ret.Length0 == shape[0] && ret.Length1 == shape[1]
    ensures forall i,j :: 0 <= i < shape[0] && 0 <= j < shape[1] ==> if shape[0] == a.Length then ret[i, j] == a[i] else  ret[i, j] == a[j]
{}