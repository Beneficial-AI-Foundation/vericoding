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

//IMPL query
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
        /* code modified by LLM (iteration 1): Added assertion to help verification */
        assert sum(a, i, k+1) == sum(a, i, k) + a[k];
        res := res + a[k];
        k := k + 1;
    }
}

//(c)

//ATOM is_prefix_sum_for
predicate is_prefix_sum_for(ps: array<int>, a: array<int>)
    reads ps, a
    requires ps.Length == a.Length + 1
{
    ps[0] == 0 && forall i :: 0 <= i < a.Length ==> ps[i+1] == ps[i] + a[i]
}

//ATOM aux
lemma aux(ps: array<int>, a: array<int>, i: int, j: int)
    reads ps, a
    requires ps.Length == a.Length + 1
    requires is_prefix_sum_for(ps, a)
    requires 0 <= i <= j <= a.Length
    ensures ps[j] - ps[i] == sum(a, i, j)
{
    if i == j {
        // Base case: sum(a, i, i) == 0 and ps[i] - ps[i] == 0
    } else {
        // Inductive case: use the fact that sum(a, i, j) == a[i] + sum(a, i+1, j)
        aux(ps, a, i+1, j);
        // Now we know ps[j] - ps[i+1] == sum(a, i+1, j)
        // And ps[i+1] == ps[i] + a[i] from is_prefix_sum_for
        // So ps[j] - ps[i] == ps[j] - ps[i+1] + ps[i+1] - ps[i] == sum(a, i+1, j) + a[i] == sum(a, i, j)
    }
}

//IMPL queryFast
method queryFast(ps: array<int>, a: array<int>, i: int, j: int) returns (res: int)
    reads ps, a
    requires ps.Length == a.Length + 1
    requires is_prefix_sum_for(ps, a)
    requires 0 <= i <= j <= a.Length
    ensures res == sum(a, i, j)
{
    /* code modified by LLM (iteration 1): Call aux lemma to establish postcondition */
    aux(ps, a, i, j);
    res := ps[j] - ps[i];
}

//ATOM Main
method Main()
{
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 1, 2, 3, 4, 5;
    
    var ps := new int[6];
    ps[0] := 0;
    ps[1] := ps[0] + a[0];
    ps[2] := ps[1] + a[1];
    ps[3] := ps[2] + a[2];
    ps[4] := ps[3] + a[3];
    ps[5] := ps[4] + a[4];
    
    var result := queryFast(ps, a, 1, 4);
    print "Sum from index 1 to 3: ", result, "\n";
}