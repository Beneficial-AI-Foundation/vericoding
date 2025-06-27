//https://numpy.org/doc/stable/reference/generated/numpy.zeros.html

//zeros(shape, dtype=float, order='C', *, like=None)

//IMPL zeros
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
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < shape[1] ==> ret[ii, jj] == 0
    {
        var j := 0;
        while j < shape[1]
            invariant 0 <= j <= shape[1]
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < shape[1] ==> ret[ii, jj] == 0
            invariant forall jj :: 0 <= jj < j ==> ret[i, jj] == 0
        {
            ret[i, j] := 0;
            j := j + 1;
        }
        i := i + 1;
    }
}