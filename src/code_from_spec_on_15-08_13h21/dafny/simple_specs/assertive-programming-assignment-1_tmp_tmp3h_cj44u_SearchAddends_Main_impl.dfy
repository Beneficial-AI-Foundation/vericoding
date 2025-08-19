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
  /* code modified by LLM (iteration 3): Fixed loop invariant to properly track searched regions */
  i := 0;
  j := |q| - 1;
  
  while i < j
    invariant 0 <= i <= j < |q|
    invariant exists ii, jj :: 0 <= ii < jj < |q| && q[ii] + q[jj] == x
    invariant forall ii, jj :: 0 <= ii < jj < |q| && (ii < i || jj > j) ==> q[ii] + q[jj] != x
  {
    if q[i] + q[j] == x {
      return i, j;
    } else if q[i] + q[j] < x {
      i := i + 1;
    } else {
      j := j - 1;
    }
  }
  
  /* code modified by LLM (iteration 3): Added proof that this point is unreachable */
  // This should never be reached due to precondition HasAddends(q, x)
  // If we reach here, i >= j, but we know there exist valid addends
  ghost var witness_i, witness_j :| 0 <= witness_i < witness_j < |q| && q[witness_i] + q[witness_j] == x;
  
  // The invariant tells us all pairs outside [i,j] don't work
  // But if i >= j, then [i,j] is empty, so all pairs have been eliminated
  // This contradicts the existence of witness pair
  assert witness_i < witness_j;
  assert witness_i < i || witness_j > j; // follows from i >= j
  assert q[witness_i] + q[witness_j] != x; // from invariant
  assert q[witness_i] + q[witness_j] == x; // from witness property
  assert false;
}

//IMPL 
method Main()
{
	var q := [1,2,4,5,6,7,10,23];
	/* code modified by LLM (iteration 1): Added explicit proofs for preconditions */
	
	// Prove Sorted(q)
	assert forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j];
	assert Sorted(q);
	
	// Prove HasAddends(q, 10) - we can see that q[2] + q[4] = 4 + 6 = 10
	assert q[2] == 4 && q[4] == 6;
	assert q[2] + q[4] == 10;
	assert 0 <= 2 < 4 < |q|;
	assert HasAddends(q, 10);
	
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