//ATOM

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}


//ATOM

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}


//IMPL

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
    i := 0;
    j := |q| - 1;
    
    while i < j
        invariant 0 <= i < j < |q|
        /* code modified by LLM (iteration 2): maintain that addends exist in the array */
        invariant HasAddends(q, x)
        /* code modified by LLM (iteration 2): ensure addends must exist within current window */
        invariant exists a, b :: i <= a < b <= j && q[a] + q[b] == x
        /* code modified by LLM (iteration 2): track eliminated pairs with reasoning about why they can't sum to x */
        invariant forall a :: 0 <= a < i ==> q[a] + q[j] < x
        invariant forall b :: j < b < |q| ==> q[i] + q[b] > x
    {
        var sum := q[i] + q[j];
        if sum == x {
            return;
        } else if sum < x {
            /* code modified by LLM (iteration 2): assert reasoning before incrementing i with bounds check */
            assert forall b :: j < b < |q| ==> q[i+1] + q[b] <= q[i+1] + q[j] <= q[i] + q[j] < x;
            i := i + 1;
        } else {
            /* code modified by LLM (iteration 2): assert reasoning before decrementing j with bounds check */
            assert forall a :: 0 <= a <= i ==> q[a] + q[j-1] >= q[i] + q[j-1] >= q[i] + q[j] > x;
            j := j - 1;
        }
    }
}