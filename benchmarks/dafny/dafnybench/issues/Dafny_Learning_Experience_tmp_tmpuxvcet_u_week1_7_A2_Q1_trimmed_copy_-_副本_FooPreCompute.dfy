// <vc-preamble>
ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
    decreases hi
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

method FooCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    decreases CountIndex
    modifies b
    ensures p == Count(CountIndex,a)
{
    assert CountIndex == 0 || (|a| == b.Length && 1<=CountIndex  <= |a|);
    assert CountIndex == 0 || (|a| == b.Length && 0<=CountIndex -1 <= |a|);
    assert CountIndex!=0 ==> |a| == b.Length && 0<=CountIndex -1 <= |a|;
    assert CountIndex == 0 ==> true && CountIndex != 0 ==> |a| == b.Length && 0<=CountIndex -1 <= |a|;
    if CountIndex == 0{
        assert true;
        assert 0 == 0;
        assert 0 == Count(0,a);
        p :=0;
        assert p == Count(CountIndex,a);
    } else{
        assert |a| == b.Length && 0<=CountIndex-1 <=|a|;
        assert (a[CountIndex-1]%2 ==0 ==>|a| == b.Length && 0<= CountIndex -1 <|a| && 1+ Count(CountIndex-1,a) == Count(CountIndex,a)) && 
        (a[CountIndex-1]%2 !=0 ==>  |a| == b.Length && 0<= CountIndex -1 <|a| && Count(CountIndex-1,a) == Count(CountIndex,a));
        if a[CountIndex-1]%2==0{
            assert |a| == b.Length && 0<= CountIndex -1 <|a| && 1+ Count(CountIndex-1,a) == Count(CountIndex,a);
            var d := FooCount(CountIndex -1,a,b);
            assert d+1 == Count(CountIndex,a);
            p:= d+1;
             assert p == Count(CountIndex,a);
        }else{
            assert |a| == b.Length && 0<= CountIndex -1 <|a| && Count(CountIndex-1,a) == Count(CountIndex,a);
            assert  |a| == b.Length && 0<= CountIndex -1 <|a| && forall p'::p' ==Count(CountIndex-1,a) ==> p'==Count(CountIndex,a);
            var d:= FooCount(CountIndex -1,a,b);
            assert d == Count(CountIndex,a);
            p:= d;
            assert p == Count(CountIndex,a);
        }
        b[CountIndex-1] := p;
        assert p == Count(CountIndex,a);

    }
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method FooPreCompute(a:array<int>,b:array<int>)
    requires a.Length == b.Length
    modifies b
// </vc-spec>
// <vc-code>
{
    var CountIndex := 1;
    while CountIndex != a.Length + 1
        decreases a.Length + 1  - CountIndex
        invariant 1 <= CountIndex <= a.Length +1;

    {   
        assert (CountIndex == 0 || (a.Length == b.Length && 1 <= CountIndex <= a.Length)) && forall a'::a' ==Count(CountIndex,a[..]) ==> a' ==Count(CountIndex,a[..]);
        var p := FooCount(CountIndex,a[..],b);
        assert 1<= CountIndex <= a.Length;
        assert 1 <= CountIndex  + 1<= a.Length +1;
        CountIndex := CountIndex +1;
        assert 1 <= CountIndex <= a.Length +1;
    }
}
// </vc-code>
