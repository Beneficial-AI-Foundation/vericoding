//ATOM
predicate IsSorted(s:seq<int>)
{
 forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

//ATOM
predicate SortSpec(input:seq<int>, output:seq<int>)
{
 && IsSorted(output)
 && multiset(output) == multiset(input)
}

//IMPL merge
method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
 requires IsSorted(a)
 requires IsSorted(b)
 ensures SortSpec(a+b, output)
{
    output := [];
    var i, j := 0, 0;
    
    while i < |a| || j < |b|
        invariant 0 <= i <= |a|
        invariant 0 <= j <= |b|
        invariant IsSorted(output)
        invariant multiset(output) == multiset(a[..i]) + multiset(b[..j])
        /* code modified by LLM (iteration 3): Fixed ordering invariant */
        invariant forall k :: 0 <= k < |output| ==> 
            (i < |a| ==> output[k] <= a[i]) &&
            (j < |b| ==> output[k] <= b[j])
    {
        if i >= |a| {
            /* code modified by LLM (iteration 3): Added assertion to help verification */
            assert j < |b|;
            output := output + [b[j]];
            j := j + 1;
        } else if j >= |b| {
            /* code modified by LLM (iteration 3): Added assertion to help verification */
            assert i < |a|;
            output := output + [a[i]];
            i := i + 1;
        } else if a[i] <= b[j] {
            output := output + [a[i]];
            i := i + 1;
        } else {
            output := output + [b[j]];
            j := j + 1;
        }
    }
    
    /* code modified by LLM (iteration 3): Final proof assertions */
    assert i == |a| && j == |b|;
    assert a[..i] == a && b[..j] == b;
    assert multiset(output) == multiset(a) + multiset(b);
    assert multiset(a) + multiset(b) == multiset(a + b);
}