method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
 ensures count == |set i | i in numbers && i < threshold|
{
    count := 0;
    var remaining := numbers;
    
    while remaining != {}
        invariant remaining <= numbers
        /* code modified by LLM (iteration 4): added invariant to track disjoint sets */
        invariant remaining * (numbers - remaining) == {}
        invariant count == |set i | i in (numbers - remaining) && i < threshold|
        decreases |remaining|
    {
        var x :| x in remaining;
        var old_remaining := remaining;
        remaining := remaining - {x};
        
        /* code modified by LLM (iteration 4): added assertion to help prove set cardinality */
        assert numbers - remaining == (numbers - old_remaining) + {x};
        assert x !in (numbers - old_remaining);
        
        if x < threshold {
            /* code modified by LLM (iteration 4): fixed assertion syntax and added proper set equality */
            assert (set i | i in (numbers - remaining) && i < threshold) == 
                   (set i | i in (numbers - old_remaining) && i < threshold) + {x};
            count := count + 1;
        } else {
            /* code modified by LLM (iteration 4): fixed assertion syntax for case when x >= threshold */
            assert (set i | i in (numbers - remaining) && i < threshold) == 
                   (set i | i in (numbers - old_remaining) && i < threshold);
        }
    }
}