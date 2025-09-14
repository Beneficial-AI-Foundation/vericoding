predicate IsEven(n: int)
{
    n % 2 == 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var res := true;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant res ==> forall j :: 0 <= j < i ==> (IsEven(j) ==> IsEven(lst[j]))
    invariant !res ==> exists j :: 0 <= j < i && IsEven(j) && !IsEven(lst[j])
  {
    if i % 2 == 0 && lst[i] % 2 != 0 {
      res := false;
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>

