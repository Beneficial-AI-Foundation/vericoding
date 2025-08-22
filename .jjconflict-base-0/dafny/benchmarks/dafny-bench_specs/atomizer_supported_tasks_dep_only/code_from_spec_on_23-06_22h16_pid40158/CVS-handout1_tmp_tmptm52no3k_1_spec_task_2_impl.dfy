/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

//ATOM sum
function sum(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j <= a.Length
{
    if (i == j) then 0
    else a[i] + sum(a, i+1, j)
}




//(b)

//ATOM query
method query(a: array<int>, i: int, j: int) returns (r: int)
    requires 0 <= i <= j <= a.Length
    ensures r == sum(a, i, j)
{
    r := 0;
    var k := i;
    while k < j
        invariant i <= k <= j
        invariant r == sum(a, i, k)
    {
        r := r + a[k];
        k := k + 1;
    }
}



//(c)

//ATOM is_prefix_sum_for
predicate is_prefix_sum_for (a: array<int>, c: array<int>)
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    reads c, a
{
    forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}


//ATOM aux
lemma aux(a: array<int>, c: array<int>, i: int, j: int)
    requires 0 <= i <= j <= a.Length
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    requires is_prefix_sum_for(a, c)
    ensures sum(a, i, j) == c[j] - c[i]
{
    if i == j {
        // Base case: sum(a, i, i) == 0 and c[i] - c[i] == 0
    } else {
        // Inductive case
        aux(a, c, i+1, j);
        // We know sum(a, i+1, j) == c[j] - c[i+1]
        // And sum(a, i, j) == a[i] + sum(a, i+1, j)
        // From is_prefix_sum_for: c[i+1] == c[i] + a[i]
        // Therefore: sum(a, i, j) == a[i] + (c[j] - c[i+1]) == a[i] + c[j] - (c[i] + a[i]) == c[j] - c[i]
    }
}



//IMPL queryFast
method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
    requires a.Length + 1 == c.Length && c[0] == 0
    requires 0 <= i <= j <= a.Length
    requires is_prefix_sum_for(a,c)  
    ensures r == sum(a, i, j)
{
    /* code modified by LLM (iteration 1): Added lemma call to establish the relationship between sum and prefix array */
    aux(a, c, i, j);
    r := c[j] - c[i];
}





//ATOM Main
method Main() {
    var a := new int[3];
    a[0], a[1], a[2] := 1, 2, 3;
    
    var c := new int[4];
    c[0], c[1], c[2], c[3] := 0, 1, 3, 6;
    
    var result := queryFast(a, c, 0, 3);
    print "Sum from 0 to 3: ", result, "\n";
}