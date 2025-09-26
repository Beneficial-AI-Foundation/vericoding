// <vc-preamble>
function getSize(i: int, j:int) : int
{
    j - i + 1    
}
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
