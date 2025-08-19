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

//IMPL 

method Main()
{
	/* code modified by LLM (iteration 1): Fixed array initialization syntax - arrays in Dafny are created with 'new' and then elements are assigned individually */
	var arr: array<int> := new int[9];
	arr[0] := 1;
	arr[1] := 1;
	arr[2] := 25;
	arr[3] := 7;
	arr[4] := 2;
	arr[5] := -2;
	arr[6] := 3;
	arr[7] := 3;
	arr[8] := 20;
	
	var idx := FindMax(arr);

	// apparently I can't assert definite values like
	// assert idx == 2
	// or assert arr[idx] == 25
}