//IMPL
method arange(start: real, stop: real, step: real) returns (ret: array<real>)
    requires if step < 0.0 then start > stop else start < stop
    requires step != 0.0
    ensures ret.Length == ((stop - start)/step).Floor 
    ensures ret.Length > 0
    ensures ret[0] == start
    ensures forall i :: 1 <= i < ret.Length ==> ret[i] - ret[i-1] == step
{
    var length := ((stop - start) / step).Floor;
    ret := new real[length];
    
    var i := 0;
    while i < length
        invariant 0 <= i <= length
        invariant forall j :: 0 <= j < i ==> ret[j] == start + step * j.real
    {
        ret[i] := start + step * i.real;
        i := i + 1;
    }
}