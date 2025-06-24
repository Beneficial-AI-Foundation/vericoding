/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

//ATOM sum

//(a)

function sum(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j <= a.Length
{
    if (i == j) then 0
    else a[i] + sum(a, i+1, j)
}




//(b)

//IMPL queryFast

method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
    requires a.Length + 1 == c.Length && c[0] == 0
    requires 0 <= i <= j <= a.Length
    requires is_prefix_sum_for(a,c)  
    ensures r == sum(a, i, j)
{
    /* code modified by LLM (iteration 1): added lemma call to establish sum relationship */
    aux(a, c, i, j);
    r := c[j] - c[i];
}



//(c)

//ATOM is_prefix_sum_for

//(c)

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
        // We know that sum(a, i+1, j) == c[j] - c[i+1] by inductive hypothesis
        // We know that c[i+1] == c[i] + a[i] by is_prefix_sum_for
        // sum(a, i, j) == a[i] + sum(a, i+1, j) by definition
        // Therefore: sum(a, i, j) == a[i] + (c[j] - c[i+1]) == a[i] + c[j] - (c[i] + a[i]) == c[j] - c[i]
    }
}



//IMPL Main

method Main()
{
    /* code modified by LLM (iteration 1): added simple test case implementation */
    var a := new int[3];
    a[0] := 1; a[1] := 2; a[2] := 3;
    var c := new int[4];
    c[0] := 0; c[1] := 1; c[2] := 3; c[3] := 6;
    
    var result := queryFast(a, c, 0, 2);
    print "Sum from index 0 to 2: ", result, "\n";
}