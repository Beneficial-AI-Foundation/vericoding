//IMPL 
method lookForMin (a: array<int>, i: int) returns (m: int)
	requires 0 <= i < a.Length
	ensures i <= m < a.Length
	ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{
	m := i;
	var j := i + 1;
	
	while j < a.Length
		invariant i <= m < a.Length
		invariant i <= j <= a.Length
		invariant forall k :: i <= k < j ==> a[k] >= a[m]
	{
		if a[j] < a[m] {
			m := j;
		}
		j := j + 1;
	}
}