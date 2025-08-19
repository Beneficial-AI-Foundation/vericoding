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

/* code modified by LLM (iteration 2): Added helper lemma to prove sorted property is maintained when appending */
lemma SortedAppendLemma(s: seq<int>, x: int)
    requires IsSorted(s)
    requires |s| == 0 || s[|s|-1] <= x
    ensures IsSorted(s + [x])
{
    if |s| == 0 {
        // Base case: empty sequence + [x] is trivially sorted
    } else {
        // Need to prove that s + [x] maintains sorted property
        var result := s + [x];
        forall i | 0 <= i < |result|-1
            ensures result[i] <= result[i+1]
        {
            if i < |s|-1 {
                // Elements within original sequence s
                assert result[i] == s[i];
                assert result[i+1] == s[i+1];
            } else if i == |s|-1 {
                // Transition from last element of s to x
                assert result[i] == s[|s|-1];
                assert result[i+1] == x;
                assert s[|s|-1] <= x;
            }
        }
    }
}

/* code modified by LLM (iteration 2): Added multiset lemmas to help with invariant proof */
lemma MultisetSliceLemma(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures multiset(s[..i+1]) == multiset(s[..i]) + multiset([s[i]])
{
    assert s[..i+1] == s[..i] + [s[i]];
}

//IMPL 
method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
 requires IsSorted(a)
 requires IsSorted(b)
// ensures IsSorted(output)
 ensures SortSpec(a+b, output)
 //decreases |a|+|b|
{
    output := [];
    var i, j := 0, 0;
    
    /* code modified by LLM (iteration 2): Enhanced loop invariants and added multiset reasoning */
    while i < |a| || j < |b|
        invariant 0 <= i <= |a|
        invariant 0 <= j <= |b|
        invariant IsSorted(output)
        invariant multiset(output) == multiset(a[..i]) + multiset(b[..j])
        invariant |output| == 0 || (i < |a| ==> output[|output|-1] <= a[i])
        invariant |output| == 0 || (j < |b| ==> output[|output|-1] <= b[j])
        decreases |a| - i + |b| - j
    {
        if i >= |a| {
            /* code modified by LLM (iteration 2): Added multiset reasoning for appending from b */
            assert j < |b|;
            if |output| > 0 {
                assert output[|output|-1] <= b[j];
            }
            SortedAppendLemma(output, b[j]);
            MultisetSliceLemma(b, j);
            assert multiset(b[..j+1]) == multiset(b[..j]) + multiset([b[j]]);
            output := output + [b[j]];
            assert multiset(output) == multiset(a[..i]) + multiset(b[..j]) + multiset([b[j]]);
            assert multiset(output) == multiset(a[..i]) + multiset(b[..j+1]);
            j := j + 1;
        } else if j >= |b| {
            /* code modified by LLM (iteration 2): Added multiset reasoning for appending from a */
            assert i < |a|;
            if |output| > 0 {
                assert output[|output|-1] <= a[i];
            }
            SortedAppendLemma(output, a[i]);
            MultisetSliceLemma(a, i);
            assert multiset(a[..i+1]) == multiset(a[..i]) + multiset([a[i]]);
            output := output + [a[i]];
            assert multiset(output) == multiset(a[..i]) + multiset(b[..j]) + multiset([a[i]]);
            assert multiset(output) == multiset(a[..i+1]) + multiset(b[..j]);
            i := i + 1;
        } else if a[i] <= b[j] {
            /* code modified by LLM (iteration 2): Added multiset reasoning for appending from a */
            if |output| > 0 {
                assert output[|output|-1] <= a[i];
            }
            SortedAppendLemma(output, a[i]);
            MultisetSliceLemma(a, i);
            assert multiset(a[..i+1]) == multiset(a[..i]) + multiset([a[i]]);
            output := output + [a[i]];
            assert multiset(output) == multiset(a[..i]) + multiset(b[..j]) + multiset([a[i]]);
            assert multiset(output) == multiset(a[..i+1]) + multiset(b[..j]);
            i := i + 1;
        } else {
            /* code modified by LLM (iteration 2): Added multiset reasoning for appending from b */
            assert b[j] < a[i];
            if |output| > 0 {
                assert output[|output|-1] <= b[j];
            }
            SortedAppendLemma(output, b[j]);
            MultisetSliceLemma(b, j);
            assert multiset(b[..j+1]) == multiset(b[..j]) + multiset([b[j]]);
            output := output + [b[j]];
            assert multiset(output) == multiset(a[..i]) + multiset(b[..j]) + multiset([b[j]]);
            assert multiset(output) == multiset(a[..i]) + multiset(b[..j+1]);
            j := j + 1;
        }
    }
    
    /* code modified by LLM (iteration 2): Added final assertions to prove postcondition */
    assert i == |a| && j == |b|;
    assert a[..i] == a && b[..j] == b;
    assert multiset(output) == multiset(a) + multiset(b);
    assert multiset(a) + multiset(b) == multiset(a + b);
}