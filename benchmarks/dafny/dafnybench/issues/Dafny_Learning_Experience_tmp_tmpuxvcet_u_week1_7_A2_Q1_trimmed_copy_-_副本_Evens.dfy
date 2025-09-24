// <vc-preamble>
ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}




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
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Evens(a:array<int>) returns (c:array2<int>)

    // modifies c
    // ensures  invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j<i ==> c[i,j] == 0
// </vc-spec>
// <vc-code>
{
     c := new int[a.Length,a.Length];
     var b := new int[a.Length];
     var foo := PreCompute(a,b); 
     var m := 0;
     while m != a.Length
        decreases a.Length - m
        modifies c
        invariant 0 <= m <= a.Length
        invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j<i ==> c[i,j] == 0
        invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j>=i ==> i>0 ==> c[i,j] == b[j] - b[i-1]
        invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j>=i ==> i == 0 ==> c[i,j] == b[j]
     {  
        var n := 0;
        while n != a.Length
            decreases a.Length - n
            modifies c
            invariant 0 <= n <= a.Length
            invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j<i ==> c[i,j] == 0
            invariant forall j:: 0 <= j <n ==> j < m ==> c[m,j] == 0
            invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j>=i ==> i>0 ==> c[i,j] == b[j] - b[i-1]
            invariant forall j:: 0 <= j <n ==> j>=m ==> m>0 ==> c[m,j] == b[j] - b[m-1]
            invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length ==> j>=i ==> i == 0 ==> c[i,j] == b[j]
            invariant forall j:: 0 <= j <n ==> j>=m ==> m==0 ==> c[m,j] == b[j]
        {   
            if (n < m) {
                c[m,n] := 0;
            }else { 
                if m > 0 {
                    c[m,n] := b[n] - b[m-1];
                }else{
                    c[m,n] := b[n];
                }
            }
            n := n + 1;
        }
        m := m + 1;
     }
}
// </vc-code>
