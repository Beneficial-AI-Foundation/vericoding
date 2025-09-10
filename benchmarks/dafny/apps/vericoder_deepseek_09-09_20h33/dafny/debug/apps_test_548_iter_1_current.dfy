predicate AllEven(a: seq<int>)
{
    forall i :: 0 <= i < |a| ==> a[i] % 2 == 0
}

predicate HasOdd(a: seq<int>)
{
    exists i :: 0 <= i < |a| && a[i] % 2 == 1
}

// <vc-helpers>
lemma AllEvenOrHasOdd(a: seq<int>)
    ensures AllEven(a) || HasOdd(a)
{
    if !AllEven(a) {
        assert exists i :: 0 <= i < |a| && a[i] % 2 == 1;
    }
}

lemma NotBoth(a: seq<int>)
    ensures !(AllEven(a) && HasOdd(a))
{
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: string)
    ensures result == "Second" <==> AllEven(a)
    ensures result == "First" <==> HasOdd(a)
    ensures result == "First" || result == "Second"
// </vc-spec>
// <vc-code>
{
    if exists i :: 0 <= i < |a| && a[i] % 2 == 1 {
        result := "First";
    } else {
        result := "Second";
    }
}
// </vc-code>

