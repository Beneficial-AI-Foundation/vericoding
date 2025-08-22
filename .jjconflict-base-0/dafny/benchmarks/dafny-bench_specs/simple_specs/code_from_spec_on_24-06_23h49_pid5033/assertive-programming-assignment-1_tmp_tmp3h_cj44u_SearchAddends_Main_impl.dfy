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


//ATOM

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{
  i := 0;
  j := 0;
  assume i < j < |q| && q[i]+q[j] == x;
  return i, j;
}


//IMPL
method Main()
{
	var q := [1,2,4,5,6,7,10,23];
	assert Sorted(q);
	/* code modified by LLM (iteration 1): Fixed HasAddends assertion with correct indices and arithmetic */
	assert HasAddends(q, 10) by {
		assert 2 < 6 < |q| && q[2] + q[6] == 4 + 10 == 14;
		assert 0 < 6 < |q| && q[0] + q[6] == 1 + 10 == 11;
		assert 1 < 6 < |q| && q[1] + q[6] == 2 + 10 == 12;
		assert 3 < 6 < |q| && q[3] + q[6] == 5 + 10 == 15;
		assert 0 < 2 < |q| && q[0] + q[2] == 1 + 4 == 5;
		assert 1 < 3 < |q| && q[1] + q[3] == 2 + 5 == 7;
		assert 2 < 3 < |q| && q[2] + q[3] == 4 + 5 == 9;
		assert 3 < 4 < |q| && q[3] + q[4] == 5 + 6 == 11;
		assert 0 < 4 < |q| && q[0] + q[4] == 1 + 6 == 7;
		assert 2 < 4 < |q| && q[2] + q[4] == 4 + 6 == 10;
	}
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