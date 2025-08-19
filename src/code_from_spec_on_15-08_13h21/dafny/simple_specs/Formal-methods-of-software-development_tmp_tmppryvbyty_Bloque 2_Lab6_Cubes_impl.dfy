// IMPL

// TODO: Hacer
// Derivar formalmente un calculo incremental de j*j*j
method Cubes (n:int) returns (s:seq<int>)
requires n >= 0
ensures |s| == n
ensures forall i:int :: 0 <= i < n ==> s[i] == i*i*i
{
    s := [];
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant |s| == j
        invariant forall i:int :: 0 <= i < j ==> s[i] == i*i*i
    {
        s := s + [j*j*j];
        j := j + 1;
    }
}