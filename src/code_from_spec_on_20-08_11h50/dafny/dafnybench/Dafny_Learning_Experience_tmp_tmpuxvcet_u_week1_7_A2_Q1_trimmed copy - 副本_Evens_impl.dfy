method ComputeCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    decreases CountIndex
    modifies b
    ensures p == Count(CountIndex,a)
{
    if CountIndex == 0{
        p :=0;
    } else{
        if a[CountIndex-1]%2==0{
            var d := ComputeCount(CountIndex -1,a,b);
            p:= d+1;
        }else{
            var d:= ComputeCount(CountIndex -1,a,b);
            p:= d;
        }
        b[CountIndex-1] := p;  
    }
}

method PreCompute(a:array<int>,b:array<int>)returns(p:nat)
    requires a.Length == b.Length 
    modifies b
    ensures (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length)) &&
    forall p::p == Count(b.Length,a[..]) ==> p==Count(b.Length,a[..])

{

    assert  (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length)) 
    && (forall p::p == Count(b.Length,a[..]) ==> p==Count(b.Length,a[..]) );
    p := ComputeCount(b.Length,a[..],b);

}

// <vc-helpers>
function Count(n: nat, a: seq<int>): nat
{
    if n == 0 then 0
    else if n > |a| then Count(|a|, a)
    else if a[n-1] % 2 == 0 then Count(n-1, a) + 1
    else Count(n-1, a)
}
// </vc-helpers>

method Evens(a:array<int>) returns (c:array2<int>)

    // modifies c
    // ensures  invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j<i ==> c[i,j] == 0
// </vc-spec>
// <vc-code>
{
  c := new int[a.Length, a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
  {
    var j := 0;
    while j < a.Length
      invariant 0 <= j <= a.Length
    {
      if j < i {
        c[i, j] := 0;
      } else {
        c[i, j] := Count(i, a[..]);
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>