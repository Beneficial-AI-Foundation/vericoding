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


//IMPL 

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
        /* code modified by LLM (iteration 1): added invariant to maintain ordering between output and remaining elements */
        invariant forall k :: 0 <= k < |output| ==> 
            (forall m :: i <= m < |a| ==> output[k] <= a[m]) && 
            (forall n :: j <= n < |b| ==> output[k] <= b[n])
    {
        if i >= |a| {
            output := output + [b[j]];
            j := j + 1;
        } else if j >= |b| {
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
    
    /* code modified by LLM (iteration 1): added assertions and lemma call to establish postcondition */
    assert i == |a| && j == |b|;
    assert a[..i] == a && b[..j] == b;
    assert multiset(output) == multiset(a) + multiset(b);
    MultisetConcatLemma(a, b);
    assert multiset(a) + multiset(b) == multiset(a + b);
}

/* code modified by LLM (iteration 1): added helper lemma to prove multiset concatenation property */
lemma MultisetConcatLemma(a: seq<int>, b: seq<int>)
    ensures multiset(a) + multiset(b) == multiset(a + b)
{
    if |a| == 0 {
        assert a + b == b;
    } else {
        var head := a[0];
        var tail := a[1..];
        assert a == [head] + tail;
        
        calc {
            a + b;
            == ([head] + tail) + b;
            == [head] + (tail + b);
        }
        
        MultisetConcatLemma(tail, b);
        
        calc {
            multiset(a) + multiset(b);
            == (multiset([head]) + multiset(tail)) + multiset(b);
            == multiset([head]) + (multiset(tail) + multiset(b));
            == multiset([head]) + multiset(tail + b);
            == multiset([head] + (tail + b));
            == multiset(a + b);
        }
    }
}