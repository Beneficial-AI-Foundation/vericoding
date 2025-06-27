//https://numpy.org/doc/stable/reference/generated/numpy.zeros.html

//zeros(shape, dtype=float, order='C', *, like=None)

method zeros (shape: array<nat>) returns (ret: array2<int>)
    requires shape.Length == 2;
    requires shape[0] > 0 && shape[1] > 0;
    ensures ret.Length0 == shape[0] && ret.Length1 == shape[1];
    ensures forall i, j :: 0 <= i < shape[0] && 0 <= j < shape[1] ==> ret[i, j ] == 0;
{}