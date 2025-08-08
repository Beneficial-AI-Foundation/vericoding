//IMPL
method clip (a: array<real>, min: real, max: real) returns (ret: array<real>)
    requires min < max
    ensures ret.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> if a[i] < min then ret[i] == min else if a[i] > max then ret[i] == max else ret[i] == a[i]
{
    ret := new real[a.Length];
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> if a[j] < min then ret[j] == min else if a[j] > max then ret[j] == max else ret[j] == a[j]
    {
        if a[i] < min {
            ret[i] := min;
        } else if a[i] > max {
            ret[i] := max;
        } else {
            ret[i] := a[i];
        }
        i := i + 1;
    }
}