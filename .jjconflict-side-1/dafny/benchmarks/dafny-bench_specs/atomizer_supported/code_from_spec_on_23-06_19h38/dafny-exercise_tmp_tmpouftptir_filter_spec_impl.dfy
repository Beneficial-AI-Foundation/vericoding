// IMPL 
method Filter(a:seq<char>, b:set<char>) returns(c:set<char>) 
ensures forall x :: x in a && x in b <==> x in c
{
    c := {};
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall x :: x in a[..i] && x in b <==> x in c
    {
        if a[i] in b {
            c := c + {a[i]};
        }
        i := i + 1;
    }
}

// IMPL 
method TesterFilter()
{
    var result := Filter(['a', 'b', 'c', 'a'], {'a', 'c'});
    assert 'a' in result;
    assert 'c' in result;
    assert 'b' !in result;
}