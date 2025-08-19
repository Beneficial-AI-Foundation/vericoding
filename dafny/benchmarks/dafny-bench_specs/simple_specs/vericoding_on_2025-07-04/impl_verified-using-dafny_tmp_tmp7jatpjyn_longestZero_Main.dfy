//ATOM
function getSize(i: int, j:int) : int
{
  j - i + 1  
}

//IMPL longestZero
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
  
  var i := 0;
  /* code modified by LLM (iteration 4): Fixed loop invariants and bounds checking */
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= sz <= a.Length
    invariant 0 <= pos < a.Length
    invariant pos + sz <= a.Length
    invariant forall k :: pos <= k < pos + sz ==> a[k] == 0
    invariant forall start, end :: (0 <= start <= end < i && getSize(start, end) > sz) ==> exists k :: start <= k <= end && a[k] != 0
  {
    if a[i] == 0 {
      var currentStart := i;
      var currentSize := 0;
      
      /* code modified by LLM (iteration 4): Fixed inner loop with correct size calculation */
      while i < a.Length && a[i] == 0
        invariant currentStart <= i <= a.Length
        invariant currentSize == i - currentStart
        invariant forall k :: currentStart <= k < i ==> a[k] == 0
        invariant 0 <= sz <= a.Length
        invariant 0 <= pos < a.Length
        invariant pos + sz <= a.Length
        invariant forall k :: pos <= k < pos + sz ==> a[k] == 0
        invariant forall start, end :: (0 <= start <= end < currentStart && getSize(start, end) > sz) ==> exists k :: start <= k <= end && a[k] != 0
      {
        i := i + 1;
        currentSize := i - currentStart;
      }
      
      /* code modified by LLM (iteration 4): Added proper update logic with bounds verification */
      if currentSize > sz {
        sz := currentSize;
        pos := currentStart;
      }
    } else {
      i := i + 1;
    }
  }
}

//IMPL Main
method Main()
{
  var a := new int[10];
  /* code modified by LLM (iteration 4): Fixed forall statement syntax and assignment */
  var k := 0;
  while k < a.Length
    invariant 0 <= k <= a.Length
    invariant forall i :: 0 <= i < k ==> a[i] == 0
  {
    a[k] := 0;
    k := k + 1;
  }
  
  a[3] := 1;
  var sz, pos := longestZero(a);
  print a[..], "\n";
  print a[pos..(sz+pos)], "\n";
}