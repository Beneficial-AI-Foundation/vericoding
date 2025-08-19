//ATOM
function isMax(m: int, numbers: seq<int>): bool
{
  m in numbers &&
  forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}

//IMPL 
method max(numbers: seq<int>) returns (result: int)
requires numbers != []
ensures isMax(result, numbers)
{
  result := numbers[0];
  var i := 1;
  
  while i < |numbers|
    invariant 1 <= i <= |numbers|
    invariant result in numbers
    invariant forall j :: 0 <= j < i ==> numbers[j] <= result
  {
    if numbers[i] > result {
      result := numbers[i];
    }
    i := i + 1;
  }
}