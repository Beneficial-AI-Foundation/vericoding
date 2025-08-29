//SPEC
//https://numpy.org/doc/2.2/reference/generated/numpy.remainder.html

//Returns the element-wise remainder of division.

method remainder(a: array<int>, b: array<int>) returns (ret: array<int>)
    requires a.Length == b.Length;
    requires forall i :: 0 <= i < b.Length ==> b[i] != 0;
    ensures ret.Length == a.Length;
    ensures forall i :: 0 <= i < b.Length ==> ret[i] == a[i] % b[i];
{}