predicate AllEven(a: seq<int>)
{
    forall i :: 0 <= i < |a| ==> a[i] % 2 == 0
}

predicate HasOdd(a: seq<int>)
{
    exists i :: 0 <= i < |a| && a[i] % 2 == 1
}

// <vc-helpers>
lemma AllEvenImpliesNotHasOdd(a: seq<int>)
  ensures AllEven(a) ==> !HasOdd(a)
{
  if AllEven(a) {
    assert forall i :: 0 <= i < |a| ==> a[i] % 2 != 1 by {
      forall i | 0 <= i < |a| ensures a[i] % 2 != 1 {
        assert a[i] % 2 == 0;
        assert a[i] % 2 != 1;
      }
    }
    assert !HasOdd(a);
  }
}

lemma Mod2NonZeroIsOne(x: int)
  ensures x % 2 != 0 ==> x % 2 == 1
{
  if x % 2 != 0 {
    assert 0 <= x % 2 < 2;
  }
}

lemma NotAllEvenImpliesHasOdd(a: seq<int>)
  ensures !AllEven(a) ==> HasOdd(a)
{
  if !AllEven(a) {
    assert exists i :: 0 <= i < |a| && a[i] % 2 != 0;
    var i :| 0 <= i < |a| && a[i] % 2 != 0;
    Mod2NonZeroIsOne(a[i]);
    assert a[i] % 2 == 1;
    assert HasOdd(a);
  }
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
  if AllEven(a) {
    AllEvenImpliesNotHasOdd(a);
    result := "Second";
  } else {
    NotAllEvenImpliesHasOdd(a);
    result := "First";
  }
}
// </vc-code>

