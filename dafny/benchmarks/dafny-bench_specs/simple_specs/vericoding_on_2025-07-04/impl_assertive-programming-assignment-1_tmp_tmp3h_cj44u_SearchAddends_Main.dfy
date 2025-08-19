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
	/* code modified by LLM (iteration 1): Added precondition checks before calling FindAddends */
	if Sorted(q) && HasAddends(q, 10) {
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
	} else {
		print "Preconditions not met for FindAddends";
	}
}