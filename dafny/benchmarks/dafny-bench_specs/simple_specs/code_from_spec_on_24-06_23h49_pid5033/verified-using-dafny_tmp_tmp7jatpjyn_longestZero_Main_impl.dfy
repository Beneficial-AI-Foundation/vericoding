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
  var currentStart := 0;
  var currentLength := 0;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= sz <= a.Length
    invariant 0 <= pos < a.Length
    invariant pos + sz <= a.Length
    invariant 0 <= currentStart <= i
    invariant 0 <= currentLength <= i - currentStart
    invariant currentStart + currentLength <= a.Length
    invariant forall k :: pos <= k < pos + sz ==> a[k] == 0
    invariant forall k :: currentStart <= k < currentStart + currentLength ==> a[k] == 0
    invariant currentLength == 0 ==> currentStart == i
    invariant currentLength > 0 ==> forall k :: currentStart <= k < currentStart + currentLength ==> a[k] == 0
    invariant forall start, end :: (0 <= start < end < i && getSize(start, end) > sz) ==> exists k :: start <= k <= end && a[k] != 0
  {
    if a[i] == 0 {
      if currentLength == 0 {
        currentStart := i;
      }
      currentLength := currentLength + 1;
      
      if currentLength > sz {
        sz := currentLength;
        pos := currentStart;
      }
    } else {
      currentLength := 0;
      currentStart := i + 1;
    }
    i := i + 1;
  }
}

//IMPL Main
method Main()
{
  var a := new int[10];
  /* code modified by LLM (iteration 1): Fixed forall statement syntax by adding ensures clause */
  forall i | 0 <= i < a.Length
    ensures a[i] == 0
  { 
    a[i] := 0;
  }
  
  a[3] := 1;
  var sz, pos := longestZero(a);
  print a[..], "\n";
  print a[pos..pos+sz], "\n";
}