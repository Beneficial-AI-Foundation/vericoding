predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}


//ATOM

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}


//IMPL FindAddends

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
	i := 0;
	j := |q| - 1;
	
	while i < j
		invariant 0 <= i < j < |q|
		/* code modified by LLM (iteration 1): replaced the problematic invariant with a stronger one that captures the two-pointer algorithm invariant - if addends exist in original array, they must be in current subarray or we can prove one exists */
		invariant HasAddends(q, x) ==> (HasAddends(q[i..j+1], x) || (exists k1, k2 :: i <= k1 < k2 <= j && q[k1] + q[k2] == x))
		/* code modified by LLM (iteration 1): added invariant to ensure eliminated elements cannot form the target sum with remaining elements */
		invariant forall k1, k2 :: (0 <= k1 < i && i <= k2 <= j) ==> q[k1] + q[k2] != x
		invariant forall k1, k2 :: (i <= k1 <= j && j < k2 < |q|) ==> q[k1] + q[k2] != x
	{
		var sum := q[i] + q[j];
		if sum == x {
			return;
		} else if sum < x {
			/* code modified by LLM (iteration 1): added assertion to help prove invariant maintenance when incrementing i */
			assert forall k :: i <= k <= j ==> q[i] + q[k] <= q[i] + q[j] < x;
			i := i + 1;
		} else {
			/* code modified by LLM (iteration 1): added assertion to help prove invariant maintenance when decrementing j */
			assert forall k :: i <= k <= j ==> q[k] + q[j] >= q[i] + q[j] > x;
			j := j - 1;
		}
	}
}