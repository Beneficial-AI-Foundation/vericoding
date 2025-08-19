//ATOM
function getSize(i: int, j:int) : int
{
  j - i + 1  
}

//IMPL 
method longestZero(a: array<int>) returns (sz:int, pos:int)  
  requires 1 <= a.Length
  ensures 0 <= sz <= a.Length
  ensures 0 <= pos < a.Length
  ensures pos + sz <= a.Length
  ensures forall i:int :: pos <= i < pos + sz ==> a[i] == 0
  ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{
  /* code modified by LLM (iteration 1): Initialize variables properly */
  sz := 0;
  pos := 0;
  
  var i := 0;
  /* code modified by LLM (iteration 1): Fixed loop invariants to handle sz = 0 case */
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= sz <= a.Length
    invariant 0 <= pos < a.Length
    invariant pos + sz <= a.Length
    invariant sz > 0 ==> forall k :: pos <= k < pos + sz ==> a[k] == 0
    invariant forall start, end :: (0 <= start <= end < i && end - start + 1 > sz) ==> exists k :: start <= k <= end && a[k] != 0
  {
    if a[i] == 0 {
      var start := i;
      var currentSz := 0;
      
      /* code modified by LLM (iteration 1): Inner loop to count consecutive zeros */
      while i < a.Length && a[i] == 0
        invariant start <= i <= a.Length
        invariant currentSz == i - start
        invariant forall k :: start <= k < i ==> a[k] == 0
        invariant start < a.Length
      {
        currentSz := currentSz + 1;
        i := i + 1;
      }
      
      /* code modified by LLM (iteration 1): Update best sequence if current is better */
      if currentSz > sz {
        sz := currentSz;
        pos := start;
      }
    } else {
      i := i + 1;
    }
  }
  
  /* code modified by LLM (iteration 1): Add assertion to help prove final postcondition */
  assert forall start, end :: (0 <= start <= end < a.Length && end - start + 1 > sz) ==> exists k :: start <= k <= end && a[k] != 0;
  
  /* code modified by LLM (iteration 1): Prove the postcondition using getSize definition */
  assert forall i, j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> 
    (0 <= i <= j-1 < a.Length && (j-1) - i + 1 > sz) ==> exists k :: i <= k <= j-1 && a[k] != 0;
  
  assert forall i, j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0;
}