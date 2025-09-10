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
lemma CountPrimitiveRootsLemma(p: int, i: int, j: int)
    requires ValidInput(p)
    requires 1 <= i < p-1
    requires 2 <= j <= i
    ensures (p-1) % j == 0 && (i+1) % j == 0 ==> false
{
}

lemma CountPrimitiveRootsLemma2(p: int, i: int)
    requires ValidInput(p)
    requires 1 <= i < p-1
    ensures (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0)) == 
            (forall j :: 2 <= j <= i ==> (p-1) % j != 0 || i % j != 0)
{
}

ghost function CountPrimitiveRoots_(p: int, i: int): (s: set<int>)
    requires ValidInput(p)
    requires 1 <= i <= p-1
    ensures s == set k | 1 <= k < i && (forall j :: 2 <= j <= k ==> !((p-1) % j == 0 && k % j == 0))
{
    if i == 1 then {}
    else CountPrimitiveRoots_(p, i-1) + (if forall j :: 2 <= j <= i-1 ==> !((p-1) % j == 0 && (i-1) % j == 0) then {i-1} else {})
}

lemma CountPrimitiveRootsPreservation(p: int, i: int)
    requires ValidInput(p)
    requires 1 <= i <= p-1
    ensures CountPrimitiveRoots_(p, i) == set k | 1 <= k < i && (forall j :: 2 <= j <= k ==> !((p-1) % j == 0 && k % j == 0))
{
    if i != 1 {
        CountPrimitiveRootsPreservation(p, i-1);
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
        var i: int := 1;
        ghost var s: set<int> := {};
        while i < p-1
            invariant 1 <= i <= p-1
            invariant s == CountPrimitiveRoots_(p, i)
            invariant result == |s|
        {
            var valid := true;
            var j: int := 2;
            while j <= i
                invariant 2 <= j <= i+1
                invariant valid ==> (forall k :: 2 <= k < j ==> !((p-1) % k == 0 && i % k == 0))
                invariant !valid ==> exists k :: 2 <= k < j && (p-1) % k == 0 && i % k == 0
            {
                if (p-1) % j == 0 && i % j == 0 {
                    valid := false;
                    break;
                }
                j := j + 1;
            }
            if valid {
                s := s + {i};
                result := result + 1;
            }
            i := i + 1;
            CountPrimitiveRootsPreservation(p, i);
            s := CountPrimitiveRoots_(p, i);
        }
    }
}
// </vc-code>

