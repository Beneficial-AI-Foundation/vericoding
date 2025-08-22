/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

//ATOM 




//(a)

function sum(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j <= a.Length
{
    if (i == j) then 0
    else a[i] + sum(a, i+1, j)
}




//(b)

//IMPL 



//(b)

method query(a: array<int>, i: int, j: int) returns (res:int)
    requires 0 <= i <= j <= a.Length
    ensures res == sum(a, i, j)
{
    res := 0;
    var k := i;
    while k < j
        invariant i <= k <= j
        invariant res == sum(a, i, k)
        decreases j - k
    {
        res := res + a[k];
        k := k + 1;
    }
}




//(c)

//ATOM 



//(c)

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    reads c, a
{
    forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}


//ATOM 

lemma aux(a: array<int>, c: array<int>, i: int, j: int)
    requires 0 <= i <= j <= a.Length
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    requires is_prefix_sum_for(a, c)
    ensures forall k: int :: i <= k <= j ==> sum(a, i, k) + sum(a, k, j) == c[k] - c[i] + c[j] - c[k] //sum(a, i, j) == c[j] - c[i]
{
    forall k: int | i <= k <= j
        ensures sum(a, i, k) + sum(a, k, j) == c[k] - c[i] + c[j] - c[k]
    {
        assert sum(a, i, k) == c[k] - c[i];
        assert sum(a, k, j) == c[j] - c[k];
    }
}



//IMPL 


method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
    requires a.Length + 1 == c.Length && c[0] == 0
    requires 0 <= i <= j <= a.Length
    requires is_prefix_sum_for(a,c)  
    ensures r == sum(a, i, j)
{
    /* code modified by LLM (iteration 1): added helper lemma call to prove correctness */
    sum_equals_prefix_diff(a, c, i, j);
    r := c[j] - c[i];
}

/* code modified by LLM (iteration 1): added helper lemma to prove sum equals prefix difference */
lemma sum_equals_prefix_diff(a: array<int>, c: array<int>, i: int, j: int)
    requires 0 <= i <= j <= a.Length
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    requires is_prefix_sum_for(a, c)
    ensures sum(a, i, j) == c[j] - c[i]
{
    if i == j {
        assert sum(a, i, j) == 0;
        assert c[j] - c[i] == 0;
    } else {
        sum_equals_prefix_diff(a, c, i+1, j);
        assert sum(a, i, j) == a[i] + sum(a, i+1, j);
        assert sum(a, i+1, j) == c[j] - c[i+1];
        assert is_prefix_sum_for(a, c);
        assert c[i+1] == c[i] + a[i];
        assert sum(a, i, j) == a[i] + (c[j] - c[i+1]);
        assert sum(a, i, j) == a[i] + c[j] - (c[i] + a[i]);
        assert sum(a, i, j) == c[j] - c[i];
    }
}





//IMPL 




method Main()
{
    var a := new int[3];
    a[0] := 1; a[1] := 2; a[2] := 3;
    
    var c := new int[4];
    c[0] := 0; c[1] := 1; c[2] := 3; c[3] := 6;
    
    /* code modified by LLM (iteration 1): proved is_prefix_sum_for using forall statement */
    assert a.Length + 1 == c.Length;
    assert c[0] == 0;
    
    forall i: int | 0 <= i < a.Length
        ensures c[i+1] == c[i] + a[i]
    {
        if i == 0 {
            assert c[1] == 1 && c[0] + a[0] == 0 + 1;
        } else if i == 1 {
            assert c[2] == 3 && c[1] + a[1] == 1 + 2;
        } else if i == 2 {
            assert c[3] == 6 && c[2] + a[2] == 3 + 3;
        }
    }
    
    assert is_prefix_sum_for(a, c);
    
    var result := queryFast(a, c, 0, 3);
    print "Sum of array elements: ", result, "\n";
}