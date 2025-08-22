//ATOM
predicate IsEven(n: int)
{
  n % 2 == 0
}


// SPEC

method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
{
}
