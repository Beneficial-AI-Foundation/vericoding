//IMPL MAXIMUM OF A SEQUENCE
method maxSeq(v: seq<int>) returns (max:int)
requires |v| >= 1
ensures forall i :: 0 <= i < |v| ==> max >= v[i]
ensures max in v
{
    max := v[0];
    var i := 1;
    while i < |v|
        invariant 1 <= i <= |v|
        invariant max in v[0..i]
        invariant forall j :: 0 <= j < i ==> max >= v[j]
    {
        if v[i] > max {
            max := v[i];
        }
        i := i + 1;
    }
}