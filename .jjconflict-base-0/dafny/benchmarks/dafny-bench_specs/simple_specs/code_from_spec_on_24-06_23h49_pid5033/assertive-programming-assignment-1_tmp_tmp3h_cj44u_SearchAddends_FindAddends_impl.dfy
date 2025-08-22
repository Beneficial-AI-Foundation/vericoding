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
	var a := 0;
	while a < |q|
		invariant 0 <= a <= |q|
		invariant forall k1, k2 :: 0 <= k1 < a && k1 < k2 < |q| ==> q[k1] + q[k2] != x
	{
		var b := a + 1;
		while b < |q|
			invariant a + 1 <= b <= |q|
			invariant forall k :: a < k < b ==> q[a] + q[k] != x
		{
			if q[a] + q[b] == x {
				i := a;
				j := b;
				return;
			}
			b := b + 1;
		}
		a := a + 1;
	}
}