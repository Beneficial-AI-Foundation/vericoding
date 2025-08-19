predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}


//ATOM

predicate HasAddends(q: seq<int>, x: int)
{
	exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}


//ATOM

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
  i := 0;
  j := 0;
  /* code modified by LLM (iteration 3): Fixed loop invariant to correctly track eliminated pairs */
  // Find the actual addends using two-pointer approach
  var left := 0;
  var right := |q| - 1;
  
  while left < right
    invariant 0 <= left <= right < |q|
    invariant HasAddends(q, x)
    invariant forall k,l :: 0 <= k < |q| && 0 <= l < |q| && k < l && (k < left || l > right) ==> q[k] + q[l] != x
    decreases right - left
  {
    if q[left] + q[right] == x {
      i := left;
      j := right;
      return;
    } else if q[left] + q[right] < x {
      left := left + 1;
    } else {
      right := right - 1;
    }
  }
  
  // This should never be reached due to precondition HasAddends(q, x)
  // But we need to satisfy the postcondition
  var witness_i, witness_j :| 0 <= witness_i < witness_j < |q| && q[witness_i] + q[witness_j] == x;
  i := witness_i;
  j := witness_j;
}


//IMPL 
method Main()
{
	/* code modified by LLM (iteration 2): Explicitly prove HasAddends by providing witness indices */
	var q := [1,2,4,5,6,7,10,23];
	
	// Verify that q is sorted
	assert Sorted(q);
	
	// Explicitly prove HasAddends by showing specific indices
	assert q[2] == 4 && q[4] == 6 && q[2] + q[4] == 10;
	assert 0 <= 2 < 4 < |q|;
	assert HasAddends(q, 10); // 4 + 6 == 10, positions 2 and 4
	
	var i,j := FindAddends(q, 10);
	print "Searching for addends of 10 in q == [1,2,4,5,6,7,10,23]:\n";
	print "Found that q[";
	print i;
	print "] + q[";
	print j;
	print "] == ";
	print q[i];
	print " + ";
	print q[j];
	print " == 10";
}