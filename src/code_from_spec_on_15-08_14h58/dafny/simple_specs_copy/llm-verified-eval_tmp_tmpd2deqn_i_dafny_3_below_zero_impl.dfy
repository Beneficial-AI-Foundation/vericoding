function sum(s: seq<int>, n: nat): int
  requires n <= |s|
{
  if |s| == 0 || n == 0 then
    0
  else
    s[0] + sum(s[1..], n-1)
}

//IMPL 
method below_zero(ops: seq<int>) returns (result: bool)
  ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
  result := false;
  var i := 0;
  
  while i <= |ops|
    invariant 0 <= i <= |ops| + 1
    invariant result <==> exists n: nat :: n < i && sum(ops, n) < 0
  {
    if sum(ops, i) < 0 {
      result := true;
      /* code modified by LLM (iteration 1): Added assertion to establish that i <= |ops| for the postcondition */
      assert i <= |ops|;
      assert sum(ops, i) < 0;
      return;
    }
    i := i + 1;
  }
}