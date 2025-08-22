//IMPL FindMax
method FindMax(a: array<int>) returns (max_idx: nat)
	requires a.Length > 0
	ensures 0 <= max_idx < a.Length
	ensures forall j :: 0 <= j < a.Length ==> a[max_idx] >= a[j]
{
	max_idx := 0;
	var i := 1;
	
	while i < a.Length
		invariant 0 <= max_idx < a.Length
		invariant 1 <= i <= a.Length
		invariant forall k :: 0 <= k < i ==> a[max_idx] >= a[k]
	{
		if a[i] > a[max_idx] {
			max_idx := i;
		}
		i := i + 1;
	}
}

//IMPL Main
method Main()
{
}