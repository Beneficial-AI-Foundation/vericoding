//IMPL
method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
 ensures count == |set i | i in numbers && i < threshold|
{
    count := 0;
    var remaining := numbers;
    
    while remaining != {}
        /* code modified by LLM (iteration 4): simplified invariant using processed set */
        invariant var processed := numbers - remaining; count == |set i | i in processed && i < threshold|
        invariant remaining <= numbers
        decreases |remaining|
    {
        var x :| x in remaining;
        remaining := remaining - {x};
        
        if x < threshold {
            count := count + 1;
        }
    }
    
    /* code modified by LLM (iteration 4): added lemma call to establish set equality */
    assert remaining == {};
    SetDifferenceEmpty(numbers, remaining);
}

/* code modified by LLM (iteration 4): helper lemma to prove set difference property */
lemma SetDifferenceEmpty<T>(s: set<T>, empty: set<T>)
    requires empty == {}
    ensures s - empty == s
{
    // Dafny can prove this automatically
}