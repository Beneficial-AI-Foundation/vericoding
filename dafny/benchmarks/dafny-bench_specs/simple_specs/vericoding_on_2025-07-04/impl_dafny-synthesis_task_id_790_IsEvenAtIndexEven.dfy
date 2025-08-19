//ATOM
predicate IsEven(n: int)
{
  n % 2 == 0
}

//IMPL 
method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
{
  result := true;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant result <==> forall j :: 0 <= j < i ==> (IsEven(j) ==> IsEven(lst[j]))
  {
    if IsEven(i) && !IsEven(lst[i]) {
      result := false;
      return;
    }
    i := i + 1;
  }
}