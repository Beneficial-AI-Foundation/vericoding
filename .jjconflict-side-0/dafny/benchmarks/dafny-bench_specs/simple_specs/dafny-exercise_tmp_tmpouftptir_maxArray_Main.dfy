//ATOM
method MaxArray(a: array<int>) returns (max:int)
requires a.Length > 0
ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
ensures exists i :: 0 <= i < a.Length && a[i] == max
{
  max := 0;
  assume forall i :: 0 <= i < a.Length ==> a[i] <= max;
  assume exists i :: 0 <= i < a.Length && a[i] ==> max;
  return max;
}


// SPEC

method Main() {
	var arr : array<int> := new int[][-11,2,42,-4];
	var res := MaxArray(arr);
}
