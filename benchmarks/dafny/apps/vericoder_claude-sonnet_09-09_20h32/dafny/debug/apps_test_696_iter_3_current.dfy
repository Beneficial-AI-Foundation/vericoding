predicate ValidInput(p: int) {
    2 <= p < 2000
}

function CountPrimitiveRoots(p: int): int
    requires ValidInput(p)
{
    if p == 2 then 1
    else |set i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))|
}

// <vc-helpers>
predicate IsPrimitiveRoot(p: int, i: int)
    requires ValidInput(p)
{
    1 <= i < p-1 && forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0)
}

lemma CountPrimitiveRootsEquivalence(p: int)
    requires ValidInput(p)
    ensures CountPrimitiveRoots(p) == |set i | IsPrimitiveRoot(p, i)|
{
    if p == 2 {
        assert CountPrimitiveRoots(p) == 1;
        assert forall i :: !IsPrimitiveRoot(p, i);
        var emptySet := set i | IsPrimitiveRoot(p, i);
        assert emptySet == {};
        assert |emptySet| == 0;
        assert false;
    } else {
        assert CountPrimitiveRoots(p) == |set i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))|;
        assert forall i :: (1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))) <==> IsPrimitiveRoot(p, i);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(p: int) returns (result: int)
    requires ValidInput(p)
    ensures result >= 0
    ensures result == CountPrimitiveRoots(p)
// </vc-spec>
// <vc-code>
{
    if p == 2 {
        result := 1;
    } else {
        result := 0;
        var i := 1;
        while i < p - 1
            invariant 1 <= i <= p - 1
            invariant result == |set k | 1 <= k < i && IsPrimitiveRoot(p, k)|
        {
            var isPrimitive := true;
            var j := 2;
            while j <= i && isPrimitive
                invariant 2 <= j <= i + 1
                invariant isPrimitive <==> forall k :: 2 <= k < j ==> !((p-1) % k == 0 && i % k == 0)
            {
                if (p-1) % j == 0 && i % j == 0 {
                    isPrimitive := false;
                }
                j := j + 1;
            }
            
            if isPrimitive {
                result := result + 1;
            }
            i := i + 1;
        }
    }
}
// </vc-code>

