function getSize(i: int, j:int) : int
{
    j - i + 1    
}

// For a given integer array, let's find the longest subesquence of 0s.
// sz: size, pos: position.   a[pos..(pos+sz)] will be all zeros

// <vc-helpers>
lemma NonzeroProvidesWitness(i:int, l:int, r:int, a: array<int>)
  requires 0 <= l <= i <= r < a.Length
  requires a[i] != 0
  ensures exists k :: l <= k <= r && a[k] != 0
{
  assert l <= i <= r && a[i] != 0;
}
// </vc-helpers>

// <vc-spec>
method longestZero(a: array<int>) returns (sz:int, pos:int)   
    requires 1 <= a.Length
    ensures 0 <= sz <= a.Length
    ensures 0 <= pos < a.Length
    ensures pos + sz <= a.Length
    ensures forall i:int  :: pos <= i < pos + sz ==> a[i] == 0
    ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var best := 0;
  var bestPos := 0;
  var cur := 0;
  var curPos := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= best <= a.Length
    invariant 0 <= cur <= a.Length
    invariant 0 <= bestPos < a.Length
    invariant 0 <= curPos <= a.Length
    invariant cur == i - curPos
    invariant bestPos + best <= a.Length
    invariant curPos + cur <= a.Length
    invariant forall k :: bestPos <= k < bestPos + best ==> a[k] == 0
    invariant forall k :: curPos <= k < curPos + cur ==> a[k] == 0
    invariant curPos == 0 || a[curPos - 1] != 0
    invariant forall l,r :: 0 <= l < r < i && getSize(l,r) > best ==> exists k :: l <= k <= r && a[k] != 0
  {
    if a[i] == 0 {
      if cur == 0 {
        curPos := i;
      }
      cur := cur + 1;
      if cur > best {
        best := cur;
        bestPos := curPos;
      }
    } else {
      // a[i] != 0
      cur := 0;
      curPos := i + 1;
    }
    i := i + 1;
  }
  sz := best;
  pos := bestPos;
}
// </vc-code>

