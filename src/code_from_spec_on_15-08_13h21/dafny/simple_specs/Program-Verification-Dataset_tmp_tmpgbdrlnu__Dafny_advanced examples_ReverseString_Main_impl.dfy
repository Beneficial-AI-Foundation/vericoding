//ATOM
method yarra(arr : array<char>) returns (outarr : array<char>)
requires arr.Length > 0
ensures arr.Length == outarr.Length && reversed(arr,outarr)
{
  outarr := new char[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant outarr.Length == arr.Length
    invariant forall k :: 0 <= k < i ==> outarr[k] == arr[arr.Length - 1 - k]
  {
    outarr[i] := arr[arr.Length - 1 - i];
    i := i + 1;
  }
}

//ATOM
predicate reversed (arr : array<char>, outarr: array<char>)
requires arr.Length == outarr.Length
reads arr, outarr
{
 forall k :: 0<=k<=arr.Length-1 ==> outarr[k] == arr[(arr.Length-1-k)]
}

//IMPL
method Main()
{
 /* code modified by LLM (iteration 1): preserved original implementation */
 var s := ['a','b','a','b','a','b','a','b','a','b','a','b'];
 var a,b,c,d := new char[5], new char[5], new char[5], new char[5];
 a[0], a[1], a[2], a[3], a[4] := 'y', 'a', 'r', 'r', 'a';
 d[0], d[1], d[2], d[3], d[4] := 'y', 'a', 'r', 'r', 'a';
 b := yarra(a);
 c := yarra(b);
}