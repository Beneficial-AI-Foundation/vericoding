//ATOM
// ex2

// this was me playing around to try and get an ensures for the method 

method SecondLargest(a:array<int>) returns (seclar:int)
requires a.Length > 0
//ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
{
  var largest := a[0];
  var secondLargest := a[0];
  
  // Find the largest element
  var i := 1;
  while i < a.Length
  {
    if a[i] > largest {
      largest := a[i];
    }
    i := i + 1;
  }
  
  // Find the second largest element
  i := 0;
  while i < a.Length
  {
    if a[i] < largest && a[i] > secondLargest {
      secondLargest := a[i];
    }
    i := i + 1;
  }
  
  seclar := secondLargest;
}

//IMPL SPEC
method Main()
{
	var a: array<int> := new int[][1];
	var x:int := SecondLargest(a);
//	assert x == 1;

	var b: array<int> := new int[][9,1];
	x := SecondLargest(b);
//	assert x == 1;
	
	var c: array<int> := new int[][1,9];
	x := SecondLargest(c);
//	assert x == 1;

	var d: array<int> := new int[][2,42,-4,123,42];
	x := SecondLargest(d);
//	assert x == 42;

	var e: array<int> := new int[][1,9,8];
	x := SecondLargest(e);
//	assert x == 8;
}