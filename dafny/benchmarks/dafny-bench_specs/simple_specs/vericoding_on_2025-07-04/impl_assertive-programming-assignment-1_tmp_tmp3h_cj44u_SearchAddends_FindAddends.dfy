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
		invariant exists i',j' :: i <= i' < j' <= j && q[i'] + q[j'] == x
	{
		if q[i] + q[j] == x {
			return;
		} else if q[i] + q[j] < x {
			i := i + 1;
		} else {
			j := j - 1;
		}
	}
}