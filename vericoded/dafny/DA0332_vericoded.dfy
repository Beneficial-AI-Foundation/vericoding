function min(a: seq<int>): int
    requires |a| > 0
    ensures min(a) in a
    ensures forall i :: 0 <= i < |a| ==> min(a) <= a[i]
{
    if |a| == 1 then a[0]
    else if a[0] <= min(a[1..]) then a[0]
    else min(a[1..])
}

// <vc-helpers>
lemma MinIsMinimal(a: seq<int>, i: int)
    requires |a| > 0
    requires 0 <= i < |a|
    ensures min(a) <= a[i]
{
    // This follows from the postcondition of min function
}

lemma MinInSequence(a: seq<int>)
    requires |a| > 0
    ensures min(a) in a
{
    // This follows from the postcondition of min function
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires |a| > 0
    requires forall i :: 0 <= i < |a| ==> a[i] > 0
    ensures result == -1 || result in a
    ensures result != -1 ==> forall i :: 0 <= i < |a| ==> a[i] % result == 0
    ensures result == -1 ==> forall x :: x in a ==> exists i :: 0 <= i < |a| && a[i] % x != 0
    ensures (forall i :: 0 <= i < |a| ==> a[i] % (min(a)) == 0) ==> result == min(a)
    ensures (exists i :: 0 <= i < |a| && a[i] % (min(a)) != 0) ==> result == -1
// </vc-spec>
// <vc-code>
{
    var m := min(a);
    var allDivisible := true;
    var i := 0;
    
    while i < |a|
        invariant 0 <= i <= |a|
        invariant allDivisible == (forall j :: 0 <= j < i ==> a[j] % m == 0)
    {
        if a[i] % m != 0 {
            allDivisible := false;
            break;
        }
        i := i + 1;
    }
    
    if allDivisible {
        result := m;
    } else {
        result := -1;
    }
}
// </vc-code>

