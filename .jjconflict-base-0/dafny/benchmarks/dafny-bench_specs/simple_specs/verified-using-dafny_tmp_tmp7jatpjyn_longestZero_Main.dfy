//ATOM
function getSize(i: int, j:int) : int
{
  j - i + 1  
}


//ATOM

// For a given integer array, let's find the longest subesquence of 0s.
// sz: size, pos: position.  a[pos..(pos+sz)] will be all zeros
method longestZero(a: array<int>) returns (sz:int, pos:int)  
  requires 1 <= a.Length
  ensures 0 <= sz <= a.Length
  ensures 0 <= pos < a.Length
  ensures pos + sz <= a.Length
  ensures forall i:int :: pos <= i < pos + sz ==> a[i] == 0
  ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{
  sz := 0;
  pos := 0;
  assume 0 <= sz <= a.Length;
  assume 0 <= pos < a.Length;
  assume pos + sz <= a.Length;
  assume forall i:int :: pos <= i < pos + sz ==> a[i] == 0;
  assume forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0;
  return sz, pos;
}


// SPEC



method Main()
{
  var a := new int[10];
  forall i | 0 <= i < a.Length
    { a[i] := 0;}
  
  a[3] := 1;
  var sz, pos := longestZero(a);
  print a[..], "\n";
  print a[pos..(sz+pos)], "\n";
}
