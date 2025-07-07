//IMPL
method zeros (shape: array<nat>) returns (ret: array2<int>)
    requires shape.Length == 2;
    requires shape[0] > 0 && shape[1] > 0;
    ensures ret.Length0 == shape[0] && ret.Length1 == shape[1];
    ensures forall i, j :: 0 <= i < shape[0] && 0 <= j < shape[1] ==> ret[i, j ] == 0;
{
    ret := new int[shape[0], shape[1]];
    
    var i := 0;
    while i < shape[0]
        invariant 0 <= i <= shape[0]
        invariant forall x, y :: 0 <= x < i && 0 <= y < shape[1] ==> ret[x, y] == 0
    {
        var j := 0;
        while j < shape[1]
            invariant 0 <= j <= shape[1]
            invariant forall x, y :: 0 <= x < i && 0 <= y < shape[1] ==> ret[x, y] == 0
            invariant forall y :: 0 <= y < j ==> ret[i, y] == 0
        {
            ret[i, j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }
}