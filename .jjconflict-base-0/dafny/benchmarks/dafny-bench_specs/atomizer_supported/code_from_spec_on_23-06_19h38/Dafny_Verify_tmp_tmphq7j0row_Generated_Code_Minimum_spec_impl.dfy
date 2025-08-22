//IMPL 
method Minimum(a: array<int>) returns (m: int) 
	requires a.Length > 0
	ensures exists i :: 0 <= i < a.Length && m == a[i]
	ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
{
	m := a[0];
	var j := 1;
	while j < a.Length
		invariant 1 <= j <= a.Length
		invariant exists i :: 0 <= i < j && m == a[i]
		invariant forall i :: 0 <= i < j ==> m <= a[i]
	{
		if a[j] < m {
			m := a[j];
		}
		j := j + 1;
	}
}