//ATOM
method FindMax(a: array<int>) returns (max_idx: nat)
	requires a.Length > 0
	ensures 0 <= max_idx < a.Length
	ensures forall j :: 0 <= j < a.Length ==> a[max_idx] >= a[j]
{
  max_idx := 0;
  assume 0 <= max_idx < a.Length;
  assume forall j :: 0 <= j < a.Length ==> a[max_idx] >= a[j];
  return max_idx;
}

//IMPL Main
method Main()
{
	var arr: array<int> := new int[][1, 1, 25, 7, 2, -2, 3, 3, 20];
	var idx := FindMax(arr);

	// apparently I can't assert definite values like
	// assert idx == 2
	// or assert arr[idx] == 25
}