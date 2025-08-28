predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>
lemma ForallImpliesForall<T>(s: seq<T>, P: int -> bool, Q: int -> bool)
    requires forall i :: 0 <= i < |s| ==> (P(i) ==> Q(i))
    ensures forall i :: 0 <= i < |s| && P(i) ==> Q(i)
{
}

lemma ForallEquivalence<T>(s: seq<T>, P: int -> bool, Q: int -> bool)
    requires forall i :: 0 <= i < |s| && P(i) ==> Q(i)
    requires forall i :: 0 <= i < |s| && !P(i) ==> true
    ensures forall i :: 0 <= i < |s| ==> (P(i) ==> Q(i))
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant forall j :: 0 <= j < i ==> (IsEven(j) ==> IsEven(lst[j]))
    {
        if IsEven(i) {
            if !IsEven(lst[i]) {
                return false;
            }
        }
        i := i + 1;
    }
    return true;
}
// </vc-code>
