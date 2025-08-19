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
  var index := 0;
  
  while index < |lst|
    invariant 0 <= index <= |lst|
    invariant result <==> forall i :: 0 <= i < index ==> (IsEven(i) ==> IsEven(lst[i]))
  {
    if IsEven(index) && !IsEven(lst[index]) {
      result := false;
      return;
    }
    index := index + 1;
  }
}