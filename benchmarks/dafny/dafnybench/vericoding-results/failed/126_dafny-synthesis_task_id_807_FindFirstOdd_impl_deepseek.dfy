predicate IsOdd(x: int)
{
    x % 2 != 0
}

// <vc-helpers>
lemma LemmaOddMod(x: int)
    ensures IsOdd(x) <==> x % 2 != 0
{
}

lemma LemmaNotOddMod(x: int)
    ensures !IsOdd(x) <==> x % 2 == 0
{
}

lemma LemmaIndexRange(a: array<int>, index: int)
    ensures 0 <= index <= a.Length
{
}

lemma LemmaForallStep(a: array<int>, idx: nat)
    requires idx < a.Length
    requires forall i :: 0 <= i < idx ==> !IsOdd(a[i])
    requires !IsOdd(a[idx])
    ensures forall i :: 0 <= i < idx + 1 ==> !IsOdd(a[i])
{
}

lemma LemmaForallExtend(a: array<int>, idx: nat)
    requires idx <= a.Length
    requires forall i :: 0 <= i < idx ==> !IsOdd(a[i])
    ensures forall i :: 0 <= i < idx ==> !IsOdd(a[i])
{
}
// </vc-helpers>

// <vc-spec>
method FindFirstOdd(a: array<int>) returns (found: bool, index: int)
    requires a != null
    ensures !found ==> forall i :: 0 <= i < a.Length ==> !IsOdd(a[i])
    ensures found ==> 0 <= index < a.Length && IsOdd(a[index]) && forall i :: 0 <= i < index ==> !IsOdd(a[i])
// </vc-spec>
// <vc-code>
{
    var idx := 0;
    found := false;
    index := 0;
    
    while idx < a.Length
        invariant 0 <= idx <= a.Length
        invariant !found ==> forall i :: 0 <= i < idx ==> !IsOdd(a[i])
        invariant found ==> (0 <= index < a.Length && IsOdd(a[index]) && forall i :: 0 <= i < index ==> !IsOdd(a[i]))
    {
        if IsOdd(a[idx]) {
            found := true;
            index := idx;
            break;
        }
        LemmaForallStep(a, idx);
        idx := idx + 1;
    }
    
    if !found {
        LemmaForallExtend(a, idx);
    }
}
// </vc-code>

