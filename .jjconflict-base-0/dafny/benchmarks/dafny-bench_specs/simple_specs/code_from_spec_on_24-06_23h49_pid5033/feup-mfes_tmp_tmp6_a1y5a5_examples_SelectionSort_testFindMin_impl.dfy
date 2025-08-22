//ATOM

// Finds the position of a miminum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
method findMin(a: array<real>, from: nat, to: nat) returns(index: nat)
 requires 0 <= from < to <= a.Length
 ensures from <= index < to
 ensures forall k :: from <= k < to ==> a[k] >= a[index]
{
  index := 0;
  assume from <= index < to;
  assume forall k :: from <= k < to ==> a[k] >= a[index];
  return index;
}

//IMPL testFindMin

method testFindMin() {
  var a := new real[3];
  a[0] := 3.0;
  a[1] := 1.0;
  a[2] := 2.0;
  
  var minIndex := findMin(a, 0, 3);
}