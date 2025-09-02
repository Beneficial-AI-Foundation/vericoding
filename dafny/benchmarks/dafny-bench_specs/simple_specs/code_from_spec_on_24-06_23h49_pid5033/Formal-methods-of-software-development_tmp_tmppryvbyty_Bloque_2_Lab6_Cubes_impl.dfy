//IMPL 
method Cubes (n:int) returns (s:seq<int>)
requires n >= 0
ensures |s| == n
ensures forall i:int :: 0 <= i < n ==> s[i] == i*i*i
{
    s := [];
    var k := 0;
    while k < n
        invariant 0 <= k <= n
        invariant |s| == k
        invariant forall i:int :: 0 <= i < k ==> s[i] == i*i*i
    {
        s := s + [k*k*k];
        k := k + 1;
    }
}